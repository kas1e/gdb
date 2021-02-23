/* Native-dependent code for AmigaOS on PowerPC
   for GDB, the GNU debugger.

   Copyright 2000, 2001, 2002 Free Software Foundation, Inc.

   This file is part of GDB.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330,
   Boston, MA 02111-1307, USA.  */

#include "defs.h"
#include "gdbcore.h"
#include "inferior.h"
#include "regcache.h"
#include "value.h"
#include "gdb_string.h"
#include "elf/mips.h"
#include "symtab.h"
#include "symfile.h"
#include "objfiles.h"
#include "buildsym.h"
#include "ppc-tdep.h"
#include "stabsread.h"
#include "gdb-stabs.h"
#include "gdbthread.h"
#include "command.h"
#include "libbfd.h"

#undef HAVE_DLFCN_H
#ifdef HAVE_DLFCN_H
#include "solib-amigaos.h"
#endif

#include <exec/execbase.h>
#include <exec/tasks.h>

#if !defined(NDEBUG)
#define FUNC  IExec->DebugPrintF("\033[37m<%s>\033[39m\n", __PRETTY_FUNCTION__);
#define FUNCX IExec->DebugPrintF("\033[37m</%s>\033[39m\n", __PRETTY_FUNCTION__);
#define dprintf(format...) {IExec->Forbid();IExec->DebugPrintF("%s: ",IExec->FindTask(NULL)->tc_Node.ln_Name);IExec->DebugPrintF(format);IExec->Permit();}
//fprintf_unfiltered(gdb_stderr, ## format); 
#else
#define dprintf(format...)
#define FUNC
#define FUNCX
#endif

#define __USE_BASETYPE__
#include <sys/time.h>
#include <proto/dos.h>
#include <proto/exec.h>
#include <proto/elf.h>

#include <exec/exec.h>
#include <exec/exectags.h>
#include <exec/ports.h>
#include <exec/interrupts.h>

#include <dos/dos.h>
#include <dos/dostags.h>
#include <dos/dosextens.h>

#include <strings.h>

#define    MSR_TRACE_ENABLE           0x00000400
#define    EXC_FPE                    0x00100000
#define    EXC_ILLEGAL                0x00080000
#define    EXC_PRIV                   0x00040000
#define    EXC_TRAP                   0x00020000
#define    MAX_DEBUG_MESSAGES         20

#define    TASK_TERMINATED            0x00000001
#define    TASK_ATTACHED              0x00000002
#define    TASK_INTERRUPTED           0x00000004
#define	   TASK_OPENLIB				  0x00000008
#define	   TASK_CLOSELIB              0x00000010

extern struct ExecBase *SysBase;

static struct target_ops amigaos_ops;

struct DebugIFace *IDebug = 0;
struct Library *ElfBase = 0;
struct ElfIFace *IElf = 0;
struct MMUIFace *IMMU = 0;

/* Hook data used by the debugger hook */
struct amigaos_hook_data
{
    struct Process *current_process;
    struct Task *debugger_task;
    struct MsgPort *debugger_port;
};

struct Task *amigaos_gdb_task = 0;

/* Message sent from debugger hook to debugger to alert debugger
   of an event that happened */
   
struct debugger_message
{
    struct Message msg;
    struct Process *process;
    uint32 flags;
	uint32 signal;
    struct Library *library;
};


struct KernelDebugMessage
{
	uint32 type;
	union
	{
		struct ExceptionContext *context;
		struct Library *library;
	} message;
};
	
static struct Hook debug_hook;
static struct amigaos_hook_data debug_data;
static struct List msg_list;

void *msg_storage = 0;
unsigned long exec_seglist = 0;
static BPTR homedir = ZERO;
void *exec_elfhandle = 0;
void *current_elfhandle = 0;
int seglist_is_mine = FALSE;
int is_attach = FALSE;

/** Contains the address of the code as specified by the elf file */
static Elf32_Addr code_elf_addr;

/** The size of the code */
static int code_size;

/** Contains the relocated address of the code (i.e., the address on which it is exectuted) */
static void *code_relocated_addr;

struct ExceptionContext exc_dummy;
struct ExceptionContext *context_ptr = &exc_dummy;

BOOL child_running = FALSE;

int debug_count = 0;
int debug_buffer[100];

extern ptid_t inferior_ptid;
static int init = FALSE;
static int inferior_created = FALSE;

static ULONG amigaos_debug_callback(struct Hook *, struct Task *, struct KernelDebugMessage *);

static void amiga_term (void);
static void amiga_init (void);

static void amigaos_open (char *name, int from_tty);
static void amigaos_close (int quitting);
static void amigaos_attach (char *args, int from_tty);
static void amigaos_detach (char *args, int from_tty);
static void amigaos_kill_inferior (void);
static int amigaos_can_run(void);
static void amigaos_resume (ptid_t ptid, int step,
                            enum target_signal signal);
static ptid_t amigaos_wait (ptid_t ptid,
                            struct target_waitstatus *status);

static void amigaos_fetch_registers (int regno);			       
static void amigaos_store_registers (int regno);
static void amigaos_prepare_to_store (void);	     
static int amigaos_xfer_memory (CORE_ADDR memaddr, char *myaddr, int len,
								int write,
								struct mem_attrib *attrib,
								struct target_ops *target);
static void amigaos_files_info (struct target_ops *target);
static void amigaos_terminal_init (void);
static void amigaos_terminal_inferior (void);
static void amigaos_terminal_ours (void);
static void amigaos_mourn_inferior (void);
static void amigaos_stop (void);
static void amigaos_terminal_info (char *args, int from_tty);
static char *amigaos_pid_to_exec_file (int pid);

static int is_process_alive(struct Process *process);

char *dwarf2_read_section (struct objfile *, asection *sectp);
void amigaos_exec_close_hook(int quitting);
void amigaos_exec_file_attach_hook(char *filename, int from_tty);


void amigaos_pre_init(void) __attribute__((constructor));
void amigaos_post_term(void) __attribute__((destructor));

void amigaos_pre_init(void)
{
    ElfBase = IExec->OpenLibrary("elf.library", 0);
    if (!ElfBase)
    	error("Can't open elf.library. How did you run *this* program ?\n");
	
    IElf = (struct ElfIFace *)IExec->GetInterface(ElfBase, "main", 1, 0);
    if (!IElf)
    	error("Can't get elf.library::main\n");
		
    IMMU = (struct MMUIFace *)IExec->GetInterface((struct Library *)SysBase, "mmu", 1, 0);
    if (!IMMU)
		error("Can't get MMU access\n");	
}

void amigaos_post_term(void)
{
    if (IElf)		IExec->DropInterface((struct Interface *)IElf);
    IElf = 0;
    
    if (ElfBase)	IExec->CloseLibrary(ElfBase);
    ElfBase = 0;
	
    if (IMMU)		IExec->DropInterface((struct Interface *)IMMU);
    IMMU = 0;
}

/**
 * Make sure that everything that can be relocated,
 * is relocated.
 *
 * @param exec_elfhandle
 */
void amigaos_relocate_elfhandle (void *exec_elfhandle)
{
    Elf32_Handle hElf = (Elf32_Handle)exec_elfhandle;
    Elf32_Shdr *pHeader;
    int i;
    uint32 nSecs;
    uint32 strtblidx; /* for debugging */
    char *strtbl; /* for debugging */

    struct TagItem tags[] =
		{
			{GST_SectionIndex,     0},
			{GST_Load,             TRUE},
			{TAG_DONE,             0}
		};
  
    /* Get number of sections in ELF file and the string
     * table index. The latter is used only for debugging
     * purposes. */
    if ((2 != IElf->GetElfAttrsTags(hElf,
    		EAT_NumSections, &nSecs,
    		EAT_SectionStringTable, &strtblidx,
    		TAG_DONE)))
    {
    	fprintf(stderr,"Cannot query elf handle\n");
    	return;
    }

    if (!(strtbl = (char*)IElf->GetSectionTags(hElf, GST_SectionIndex, strtblidx, TAG_DONE)))
    {
    	fprintf(stderr,"Unable to get string table\n");
    	return;
    }

    /* Go through all sections, and make sure they are loaded and relocated */
    for (i = 1; i < nSecs; i++)
    {
		if (!(pHeader = IElf->GetSectionHeaderTags(hElf, GST_SectionIndex, i, TAG_DONE)))
			continue;

		/* We also keep track, where the executable section is located
		 * which the base address is.
		 */
		if (pHeader->sh_flags & SWF_EXECINSTR)
		{
			code_elf_addr = pHeader->sh_addr;
			code_size = pHeader->sh_size;
			code_relocated_addr = IElf->GetSectionTags(hElf,
					GST_SectionIndex, i,
					TAG_DONE);

			dprintf("Executable section (0x%x/%d bytes) starts at %p\n",(int)code_elf_addr,code_size,code_relocated_addr);
		}

		/* If this is a rela section, relocate the related section */
		if (pHeader && (pHeader->sh_type == SHT_RELA))
		{
			Elf32_Shdr *pRefHeader;
      
			/* Get the section header to which this rela section refers. This is the one we want
			 * to relocate. Make sure that it exists. */
			pRefHeader = IElf->GetSectionHeaderTags(hElf, GST_SectionIndex, pHeader->sh_info, TAG_DONE);

			/* But we don't need to do anything, if this has the SWF_ALLOC, as this case
			 * has already been handled by LoadSeg. Sections that bear debugging information
			 * (e.g., drawf2 ones) don't come with that flag.
			 */
			if (pRefHeader && !(pRefHeader->sh_flags & SWF_ALLOC))
			{
				dprintf("Relocating section \"%s\" (index %d) which is referred by section \"%s\" (index %d)\n",
						&strtbl[pRefHeader->sh_name], pHeader->sh_info,
						&strtbl[pHeader->sh_name],i);
				tags[0].ti_Data = pHeader->sh_info;
				if (!IElf->RelocateSection(hElf, tags))
				{
					fprintf(stderr,"Section %s (index %d) could not been relocated.\n",&strtbl[pRefHeader->sh_name],(int)pHeader->sh_info);
				}
			}
		}
    }
}

/**
 * Called when a new executable is loaded. On AmigaOS, it is better
 * to consult dos.library for this requirement.
 *
 * @param filename
 * @param from_tty
 */
void amigaos_exec_file_attach_hook(char *filename, int from_tty)
{
	struct PseudoSegList *seglist;

    if (!is_attach)
    {
	BPTR filelock;
        exec_seglist = IDOS->LoadSeg(filename);

        if (exec_seglist == 0)
			error ("\"%s\": not an executable file\n", filename);

        seglist_is_mine = TRUE;

    	if( (filelock = IDOS->Lock(filename,SHARED_LOCK)) != 0)
	{
    		homedir = IDOS->ParentDir(filelock);
    		IDOS->UnLock(filelock);
    	}
    }

	dprintf("Getting elf handle for seglist %p\n", exec_seglist);
    IDOS->GetSegListInfoTags(exec_seglist,
							 GSLI_ElfHandle, &exec_elfhandle,
							 GSLI_Native, &seglist,
							 TAG_DONE);

	if (exec_elfhandle == 0)
	{
		current_elfhandle = exec_elfhandle;
		return;
// FIXME: What is this?
		if (!is_attach)
			IDOS->UnLoadSeg(exec_seglist);

		exec_seglist = 0;
		error ("\"%s\": not a PowerPC executable\n", filename);
    }

	dprintf("Code starts at %p\n",seglist->ps_Entry);
    current_elfhandle = IElf->OpenElfTags(OET_ElfHandle, exec_elfhandle, TAG_DONE);
    exec_elfhandle = current_elfhandle;
    amigaos_relocate_elfhandle(exec_elfhandle);
}

/**
 * Oposite of amigaos_exec_file_attach_hook().
 *
 * @param quitting
 */
void amigaos_exec_close_hook(int quitting)
{
    if (exec_elfhandle != 0)
    {
        IElf->CloseElfTags((Elf32_Handle)exec_elfhandle,
						   CET_ReClose,    TRUE,
						   TAG_DONE);
        exec_elfhandle = 0;
    }

    if (exec_seglist != 0 && seglist_is_mine)
    {
        IDOS->UnLoadSeg(exec_seglist);
        exec_seglist = 0;
    }
}
/**
 * This is a hook hack that is called for each symbol to recover the real address.
 *
 * @param name
 * @return
 */
CORE_ADDR amigaos_get_symbol_addrs_hook(const char *name)
{
	struct Elf32_SymbolQuery query;
    Elf32_Handle hElf = (Elf32_Handle)exec_elfhandle;

    if (!hElf ) return 0;

	query.Flags = ELF32_SQ_BYNAME;
	query.Name = (char*)name;
	IElf->SymbolQuery(hElf,1,&query);

	if (query.Found)
	{
		dprintf("Name=%s Value=%p st_value=%p size=%p shndx=%p\n",name,(void*)query.Value,(void*)query.Sym.st_value,query.Sym.st_size,query.Sym.st_shndx);
		return query.Value;
	}
	return 0;
}

/**
 * Find a section matching the offset and size.
 *
 * @param hElf
 * @param offset
 * @param size
 * @return
 */
static int amigaos_find_section_by_offset_size(Elf32_Handle hElf, uint32 offset, uint32 size)
{
    int i;
    uint32 nSecs;
    Elf32_Shdr *pHeader;
 
    dprintf("amigaos_find_section_by_offset_size(hElf=%p,offset=0x%x,size=%d)\n",hElf,offset,size);
 
    IElf->GetElfAttrsTags(hElf, EAT_NumSections, &nSecs, TAG_DONE);
    if (nSecs <= 0)
		return 0;
     
    for (i = 1; i < nSecs; i++)
    {
		uint32 upper, lower;
     
		pHeader = IElf->GetSectionHeaderTags(hElf, GST_SectionIndex, i, TAG_DONE);
     
		if (pHeader && pHeader->sh_type != SHT_NOBITS)
		{
			upper = pHeader->sh_offset + pHeader->sh_size;
			lower = pHeader->sh_offset;
	
			if (lower <= offset && offset < upper)
			{
				dprintf("Found matching header for section %d (offset %x)\n", i, (int)pHeader->sh_offset);
				return i;
			}
		}
    }
  
    return 0;
}

/**
 * Hack to support relocation of sections. Called from symfile.c
 *
 * @param abfd
 * @param sectp
 * @param buf
 * @return
 */
bfd_byte *amigaos_relocate_section (bfd *abfd, asection *sectp, bfd_byte *buf)
{
	bfd_byte *contents;

    int i;
    int nIndex;
    APTR pSection;
    bfd_size_type size = bfd_get_section_size (sectp);
    int offset = sectp->filepos;
    Elf32_Handle hElf = (Elf32_Handle)current_elfhandle;
    if (size == 0) return NULL;
    if (!hElf) return NULL;

	if (!buf) contents = bfd_malloc(size);
	else contents = buf;

    dprintf("amigaos_relocate_section() name = %s\n",sectp->name);

    /* Find the section header for this section */
    nIndex = amigaos_find_section_by_offset_size(hElf, (uint32)offset, (uint32)size);

    if (nIndex == 0)
    {
		error ("Dwarf Error: Can't find a section from '%s'",
			   bfd_get_filename (abfd));
		return NULL;
    }

    /* Copy the sections from the loaded image */
    pSection = IElf->GetSectionTags(hElf, GST_SectionIndex, nIndex, TAG_DONE);
    if (!pSection)
    {
		error ("Dwarf Error: Can't copy DWARF data from '%s'",
			   bfd_get_filename (abfd));
		return NULL;
    }

    memcpy(contents, pSection, size);
	return contents;
}

/**
 * Read the contents of the section at OFFSET and of size SIZE from the
 * object file specified by OBJFILE into the psymbol_obstack and return it.
 *
 * @param objfile
 * @param sectp
 * @return
 *
 * @note originally, this resides in dwarf2read.c but needs to be overwritten,
 * as otherwise relocation won't be taken into account.
 */
char *dwarf2_read_section (struct objfile *objfile, asection *sectp)
{
    bfd *abfd = objfile->obfd;
    char *buf;
    int i;
    int nIndex;
    APTR pSection;
    bfd_size_type size = bfd_get_section_size (sectp);
    int offset = sectp->filepos;
    Elf32_Handle hElf = (Elf32_Handle)current_elfhandle;
    if (size == 0)
		return NULL;
		
    if (!hElf)
    		return NULL;

    buf = (char *) obstack_alloc (&objfile->objfile_obstack, size);
    dprintf("dwarf2_read_section() name = %s\n",sectp->name);
    /* Find the section header for this section */
    nIndex = amigaos_find_section_by_offset_size(hElf, (uint32)offset, (uint32)size);
  
    if (nIndex == 0)
    {    
		buf = NULL;
		error ("Dwarf Error: Can't identify DWARF data from '%s'",
			   bfd_get_filename (abfd));
    }
  
    /* Copy the sections from the loaded image */
    pSection = IElf->GetSectionTags(hElf, GST_SectionIndex, nIndex, TAG_DONE);
    if (!pSection)
    {
		buf = NULL;
		error ("Dwarf Error: Can't copy DWARF data from '%s'",
			   bfd_get_filename (abfd));
    }
  
    memcpy(buf, pSection, size);
       
    return buf;
}
      

/**
 * Initialize message storage. msg_list contains empty messages
 * that are taken from the queue by the debugger hook and sent as messages
 * to the debugger itself.
 */
static void init_msg_storage (void)
{
    struct debugger_message *msg;
    int i;

    if (msg_storage)
		return;
    
    if (!(msg_storage = IExec->AllocVec(MAX_DEBUG_MESSAGES * sizeof(struct debugger_message), MEMF_PUBLIC)))
		error ("Can't allocate memory for messages\n");  

    IExec->NewList(&msg_list);
  
    msg = (struct debugger_message *)msg_storage;
    for (i = 0; i < MAX_DEBUG_MESSAGES; i++)
    {
		IExec->AddHead(&msg_list, (struct Node *)msg);
		msg++;
    }
}

/**
 * Free message list memory
 */
static void term_msg_storage (void)
{
    if (msg_storage)
    {
		IExec->NewList(&msg_list);
		IExec->FreeVec(msg_storage);
		msg_storage = NULL;
    }
}

/**
 * Get an empty message and initialize it.
 * @return
 */
static struct debugger_message *get_msg_packet (void)
{
    struct debugger_message *msg;

    msg = (struct debugger_message *)IExec->RemHead(&msg_list);

    msg->msg.mn_Node.ln_Type = NT_MESSAGE;
    msg->msg.mn_Node.ln_Name = 0;
    msg->msg.mn_ReplyPort = 0;
    msg->msg.mn_Length = sizeof(struct debugger_message);
    msg->process = 0;
   
    return msg;
}

/**
 * Return a message to the pool. Note that we disable here so that we're not
 * interrupted. Can't use semaphores because get_msg_packet is called during an
 * exception.
 *
 * @param msg
 */
void drop_msg_packet(struct debugger_message *msg)
{
    if (msg)
    {
		IExec->Disable();
		IExec->AddTail(&msg_list, (struct Node *)msg);
		IExec->Enable();
    }
}

/* See if the process is still in any list (Suspend is searched first,
   as it's the most likely place if a message was sent on my_process's behalf */
   
static int is_process_alive(struct Process *my_process)
{
    struct Node *process;
	struct Task *me = (struct Task *)my_process;

//printf("DEBUG: is_process_alive()\n");

	if( child_running )
		return TRUE;
	else
		return FALSE;

    IExec->Disable();

//***NB: this is probably wrong...
/* 	switch ((enum enTaskState)(me->tc_State))
	{
		case TS_ADDED:
		case TS_RUN:
		case TS_READY:
		case TS_WAIT:
		case TS_EXCEPT:
		case TS_SUSPENDED:
			IExec->Enable();
			return TRUE;
			break;
		default:
			IExec->Enable();
			return FALSE;
			break;
	}
*/

/* FIXME FIXME FIXME
    for (process = ((struct ExecBase *)SysBase)->TaskSuspend.lh_Head;
		 process->ln_Succ;
		 process = process->ln_Succ)
    {
		if (process == (struct Node *)my_process)
		{
			IExec->Enable();
			return TRUE;
		}
    }
 */
if((enum enTaskState)(me->tc_State) == TS_SUSPENDED)
{
	IExec->Enable();
	return TRUE;
}


    for (process = SysBase->TaskWait.lh_Head;
		 process->ln_Succ;
		 process = process->ln_Succ)
    {
		if (process == (struct Node *)my_process)
		{
			IExec->Enable();
			return TRUE;
		}
    }
  
    for (process = SysBase->TaskReady.lh_Head;
		 process->ln_Succ;
		 process = process->ln_Succ)
    {
		if (process == (struct Node *)my_process)
		{
			IExec->Enable();
			return TRUE;
		}
    }

    IExec->Enable();
  
    return FALSE;
}


/**
 * Map a trap number to a GDB signal.
 *
 * @param context
 * @param flags
 * @return
 */
static int trap_to_signal(struct ExceptionContext *context, uint32 flags)
{
	dprintf("trap_to_signal(flags=0x%x)\n",flags);

    if (!context || (flags & TASK_TERMINATED))
		return TARGET_SIGNAL_QUIT;

    dprintf("traptype = 0x%x\n",context->Traptype);
    switch (context->Traptype)
    {
    case 0x200:
    case 0x300:
		return TARGET_SIGNAL_SEGV;
    case 0x400:
    case 0x600:
		return TARGET_SIGNAL_BUS;
    case 0x500:
		return TARGET_SIGNAL_INT;
    case 0x700: 
		if (context->msr & EXC_FPE)
			return TARGET_SIGNAL_FPE;
		else if (context->msr & EXC_ILLEGAL)
			return TARGET_SIGNAL_ILL;
		else if (context->msr & EXC_PRIV)
			return TARGET_SIGNAL_ILL;
		else
			return TARGET_SIGNAL_TRAP;
    case 0x800:
		return TARGET_SIGNAL_FPE;
    case 0x900:
		return TARGET_SIGNAL_ALRM;      
    case 0xa00:
    case 0xb00:
		return TARGET_SIGNAL_ILL;
    case 0xc00:
		return TARGET_SIGNAL_CHLD;
    case 0xd00:
		return TARGET_SIGNAL_TRAP;
    case 0xe00:
		return TARGET_SIGNAL_FPE;
    default:
		return -1;
    }
}  
      
/* Initialize everything needed to debug a task */

void 
amiga_init(void)
{
//printf("DEBUG: amiga_init()\n");

    if (init == TRUE)
		return;
    
    /* Get the debugger interface */
    IDebug = (struct DebugIFace *)IExec->GetInterface((struct Library *)SysBase, "debug", 1, 0);
    if (!IDebug)
		error ("Can't find kernel's debugger interface\n");
    
    /* Initialize the hook and data structure */
    debug_data.current_process = 0;
    debug_data.debugger_port = IExec->CreatePort("GDB", 0L);
    debug_data.debugger_task = IExec->FindTask(NULL);
  
//    IExec->DebugPrintF("I am %p\n", debug_data.debugger_task);
    init_msg_storage();
  
    debug_hook.h_Entry = (ULONG (*)())amigaos_debug_callback;
    debug_hook.h_Data = (APTR)&debug_data;
   
   	amigaos_gdb_task = IExec->FindTask(0);
    //IDebug->AddDebugHook(amigaos_gdb_task, &debug_hook);
   
    init = TRUE;
} 

void 
amiga_term(void)
{
//printf("DEBUG: amiga_term()\n");

    struct debugger_message *msg;
  
    if (init == FALSE)
		return;
    
    /* Clear the debug hook (necessary to avoid the shell reusing it) */ 
    IDebug->AddDebugHook(amigaos_gdb_task, NULL);
    
    /* Free pending messages and port */
    while ((msg = (struct debugger_message *)IExec->GetMsg(debug_data.debugger_port)))
		drop_msg_packet(msg);

    IExec->DeletePort(debug_data.debugger_port);
  
  	if (IDebug)
	    IExec->DropInterface((struct Interface *)IDebug);
  
    term_msg_storage();
  
    init = FALSE;
}

/* Check for an absolute path name. A path is absolute if there's no slash
   encountered before the first colon */
   
int 
amiga_is_absolute_path(const char *f)
{
//printf("\nDEBUG: amiga_is_absolute_path()\n");
//printf("       f=%s\n", f);

    int i;
    for (i = 0; i < strlen(f); i++)
    {
		/* If we reach a slash, it's not absolute */
		if (f[i] == '/') 
			return 0;

		/* Otherwise, if we reach a colon, it is */
		if (f[i] == ':')
			return 1;
    }	
   
    /* It's a plain file name */
    return 0;
}
  

/**
 * The debugger hook.
 * Checks if the currentTask is under our control, and if yes, sends a message to
 * the debugger indicating that a task under our control has caused a "signal".
 * Returning 1 will tell the system to suspend the task until further notice, while
 * returning 0 will let it have it...
 *
 * @param hook
 * @param currentTask
 * @param dbgmsg
 * @return
 */
ULONG amigaos_debug_callback(struct Hook *hook, struct Task *currentTask,
					   struct KernelDebugMessage *dbgmsg)
{

    struct amigaos_hook_data *debug_data = (struct amigaos_hook_data *)hook->h_Data;
    struct ExecIFace *IExec = (struct ExecIFace *)SysBase->MainInterface;
	struct debugger_message *msg;
	
 	/* Never suspend if the signalling task is gdb */
 	if (currentTask != (struct Task *)debug_data->current_process)
 		return 0;
	dprintf("amigaos_debug_callback(): %4d from task: %p\n",dbgmsg->type,currentTask);
 		
	/* It's our current target, send a message */
	msg = get_msg_packet();
	msg->process = (struct Process *)currentTask;

 	dprintf("dbmsg->type = %ld, msg = %p\n", dbgmsg->type, msg);

	if (debug_count < 100)
		debug_buffer[debug_count] = dbgmsg->type;
	debug_count++;

  	switch (dbgmsg->type)
   	{
   		case DBHMT_REMTASK:
			/* The task is terminating */			
			dprintf("Removing task\n");	
			msg->flags = TASK_TERMINATED;
			msg->signal = -1;
			IExec->PutMsg(debug_data->debugger_port, (struct Message *)msg);
			return 1;
			
		case DBHMT_EXCEPTION:
			/* Copy exception context */
			exc_dummy = *dbgmsg->message.context;

			dprintf("ip = %p, lr = %p, r1 = %p\n", 
					dbgmsg->message.context->ip, 
					dbgmsg->message.context->lr,
					dbgmsg->message.context->gpr[1]);
			msg->flags = 0;
			msg->signal = trap_to_signal(context_ptr, msg->flags);
			IExec->PutMsg(debug_data->debugger_port, (struct Message *)msg);
			return 1;
#if 0
		case DBHMT_OPENLIB:
			/* We're opening a new library */
			msg->flags = TASK_OPENLIB;
			msg->signal = -1;
			msg->library = dbgmsg->message.library;
			
			dprintf("Task that opened lib: %08x\n",msg->process);
			
			IExec->PutMsg(debug_data->debugger_port, (struct Message *)msg);
			
			return 1;
#endif
#if 0			
		case DBHMT_CLOSELIB:
			/* Closing a library */
			msg->flags = TASK_CLOSELIB;
			msg->library = dbgmsg->message.library;
			IExec->PutMsg(debug_data->debugger_port, (struct Message *)msg);
			
			return 1;
#endif
		case DBHMT_ADDTASK:

		default:
			drop_msg_packet(msg);
			
			return 0;
	}
	
	return 0;
}




static void
amigaos_open(char *name, int from_tty)
{
//printf("DEBUG: amigos_open()\n");

    FUNC;
  
    dprintf("name = %s, from_tty = %d\n", name, from_tty);
  
    amiga_init();
  
    FUNCX;
}


static void 
amigaos_close(int quitting)
{
//printf("DEBUG: amigaos_close()\n");

    FUNC;
 
	int i; 
    printf("quitting = %d\n", quitting);

    amiga_term();
  
    FUNCX;
}


struct Process *find_process_by_name(char *name)
{
    struct Node *process;

//printf("DEBUG: find_process_by_name()\n");

	return (struct Process *)IExec->FindTask(name);

/*    IExec->Disable();
  
    for (process = ((struct ExecBaseInternal *)SysBase)->TaskSuspend.lh_Head;
		 process->ln_Succ;
		 process = process->ln_Succ)
    {
		if (strcasecmp(process->ln_Name, name) == 0)
		{
			IExec->Enable();
			return (struct Process *)process;
		}
    }
 
    for (process = SysBase->TaskWait.lh_Head;
		 process->ln_Succ;
		 process = process->ln_Succ)
    {
		if (strcasecmp(process->ln_Name, name) == 0)
		{
			IExec->Enable();
			return (struct Process *)process;
		}
    }
  
    for (process = SysBase->TaskReady.lh_Head;
		 process->ln_Succ;
		 process = process->ln_Succ)
    {
		if (strcasecmp(process->ln_Name, name) == 0)
		{
			IExec->Enable();
			return (struct Process *)process;
		}
    }
  
    IExec->Enable();
*/  
    return (struct Process *)process;
}


static BPTR 
get_seglist(struct Process *pProcess)
{
    uint32 *array;
    BPTR segList;
 
 //printf("DEBUG: get_seglist()\n");
  
    /* Can only do that for processes right now */
    if (pProcess->pr_Task.tc_Node.ln_Type != NT_PROCESS)
    {
		return 0;
    }
  
    /* Get the seglist of the process, and re-open it's elf file */
    array = BADDR(pProcess->pr_SegArray);
    segList = array[3];

    /* If the seglist is 0, it's been shell launched, so we need to
       retrieve it's cli */
    if (segList == 0)
    {
		struct CommandLineInterface *cli = BADDR(pProcess->pr_CLI);
		if (!cli)
			return 0;
	
		segList = cli->cli_Module;
    }
  
    return segList;
}
  
static char *
amigaos_pid_to_exec_file (int pid)
{
//printf("DEBUG: amigaos_pid_to_exec_file()\n");

    struct Process *pProcess = (struct Process *)pid;
    char *filename = 0;
    BPTR segList;
    Elf32_Handle hElf;
  
    FUNC; 
    dprintf("pid = %x\n", pid);
  
    segList = get_seglist(pProcess);
  
    dprintf("process = %p, seglist = %08lx\n", pProcess, segList);
   
    IDOS->GetSegListInfoTags(segList, 
							 GSLI_ElfHandle,      &hElf,
							 TAG_DONE);

    if (!hElf)
    {
		FUNCX;
		return 0;
    }
    			   
    hElf = IElf->OpenElfTags(OET_ElfHandle, exec_elfhandle, TAG_DONE);

    IElf->GetElfAttrsTags((Elf32_Handle)exec_elfhandle, 
						  EAT_FileName, &filename, 
						  TAG_DONE);
	
    FUNCX;							
    return filename;				
}				
				
  
static void 
amigaos_attach (char *args, int from_tty)
{
    struct Process *pProcess;
    uint32 *array;
    struct debugger_message *msg;
	struct PseudoSegList *seglist;

//printf("DEBUG: amigaos_attach(): %s\n", args);


    FUNC; 
    dprintf("args = %s, from_tty = %d\n", args, from_tty);
  
    if (!args)
		error_no_arg("Need a process address or process name\n");
  
    amiga_init();

    /* Get either by address, or by name */    
    if (args[0] == '0' && args[1] == 'x')
    {
		pProcess = (struct Process *)strtol(args, 0, 0);  
    }
    else
    {
		pProcess = find_process_by_name(args);
    }
  
    if (pProcess == 0)
    {
		error ("Can't find process \"%s\"\n", args);
    }
  
	dprintf("Debugging process %p\n", pProcess);
  
    /* Can only debug processes right now */
    if (pProcess->pr_Task.tc_Node.ln_Type != NT_PROCESS)
    {
		error ("Can't find debug info for task \"%s\"\n", args);
    }
          
    /* Get the seglist and elf handle of the process */
    exec_seglist = get_seglist(pProcess);
  
    if (!exec_seglist)
    {
		error ("Can't find debug info for task \"%s\"\n", args);
    }

    seglist_is_mine = FALSE;

    IDOS->GetSegListInfoTags(exec_seglist, 
							 GSLI_ElfHandle, &exec_elfhandle,
							 GSLI_Native, &seglist,
							 TAG_DONE);

    if (!exec_elfhandle)
    {
		exec_seglist = 0;
		error ("Process \"%s\" is no ELF binary\n", args);
    }

	current_elfhandle = exec_elfhandle;
	
    dprintf("process seglist = %lx, elfhandle = %p\n", exec_seglist, exec_elfhandle);
  
    /* Suspend the task */
    dprintf("Process state: %d\n",pProcess->pr_Task.tc_State);
    if (pProcess->pr_Task.tc_State == TS_READY || pProcess->pr_Task.tc_State == TS_WAIT)
    {
		dprintf("Suspending task %p\n", pProcess);
		IExec->SuspendTask((struct Task *)pProcess, 0);
    }
  
    /* Send attach message */
    dprintf("Sending attach message\n"); 
    msg = get_msg_packet();
    msg->process = (struct Process *)pProcess;
    msg->flags = TASK_ATTACHED;
    IExec->PutMsg(debug_data.debugger_port, (struct Message *)msg);
     
    /* See if the process is crashed, and send the crash as another message */
					/*
					if (pProcess->pr_Task.tc_State == TS_CRASHED)
					{
					msg = get_msg_packet();
					msg->process = (struct Process *)pProcess;
					msg->flags = 0;
					IExec->PutMsg(debug_data.debugger_port, (struct Message *)msg);
					}*/
    
    if(pProcess->pr_Task.tc_State == TS_CRASHED)
    {
    	pProcess->pr_Task.tc_State = TS_SUSPENDED;
    }
    IDebug->AddDebugHook((struct Task *)pProcess, &debug_hook);

    debug_data.current_process = pProcess;
    
    dprintf("push_target\n");
    push_target(&amigaos_ops);
    dprintf("clear_proceed_status\n");
    clear_proceed_status ();
    dprintf("insert_breakpoints\n");
    insert_breakpoints ();     
  
    inferior_ptid = pid_to_ptid ((int)debug_data.current_process);
  
    dprintf("add_thread\n");
    add_thread(inferior_ptid);
  
    inferior_created = TRUE;  
    
    dprintf("attaching complete\n");  
    is_attach = TRUE;
  
    FUNCX;
}


static void 
amigaos_detach (char *args, int from_tty)
{
//printf("DEBUG: amigaos_detach()\n");

    FUNC;
  
    dprintf("args = %s, from_tty = %d\n", args, from_tty);
  
    if (is_attach)
    {     
		IExec->RestartTask((struct Task *)debug_data.current_process, 0);
		debug_data.current_process = 0;
		inferior_created = FALSE;
		is_attach = FALSE;
		unpush_target (&amigaos_ops);
        
		amigaos_exec_close_hook(0);
    }

    FUNCX;  
}

static int
amigaos_can_run (void)
{
//printf("DEBUG: amigaos_can_run()\n");

    return 1;
}

static void
amigaos_create_inferior (char *exec_file, char *args, char **env, int from_tty)
{
    char *io_desc;

    FUNC;
  
    dprintf("Creating inferior process: exec_file = %s, args = %s, env = %p, from_tty = %ld\n", exec_file, args, env, from_tty);
  
    if (inferior_created)
    {
		printf_unfiltered("A program is already running:\n");
		target_files_info();
		if (query("Kill it? "))
		{
			amigaos_stop();
			amigaos_kill_inferior();
		}
		else
			error ("Program not killed\n");
    }
  
    amiga_init();
  
    if (exec_file == 0)
		exec_file = get_exec_file(1);
     
    push_target(&amigaos_ops);
    clear_proceed_status ();
    insert_breakpoints ();

	IExec->Forbid();  // Make sure we can suspend the task before it starts running
    debug_data.current_process = IDOS->CreateNewProcTags(
			NP_Seglist,         exec_seglist,
			NP_FreeSeglist,     FALSE,
//			NP_Child,			TRUE,
			NP_Name,            exec_file,
			NP_Cli,             TRUE,
			NP_Arguments,       args,
			NP_Input,	    	IDOS->Input(),
			NP_CloseInput,      FALSE,
			NP_Output,          IDOS->Output(),
			NP_CloseOutput,     FALSE,
			NP_Error,           IDOS->ErrorOutput(),
			NP_CloseError,      FALSE,
			(homedir ? NP_HomeDir: TAG_IGNORE),homedir,
			TAG_DONE
		);

     if (debug_data.current_process)
    {
		dprintf("Process created: %p\n", debug_data.current_process)
		dprintf("Task: %p\n", IExec->FindTask(exec_file));
    }
    else
    {			    
		error ("Can't create process\n");
    }

    dprintf("Suspending Task\n");
    IExec->SuspendTask((struct Task *)debug_data.current_process,0);
	IExec->Permit();  

	/* Dont reuse this, note that the home dir get's unlocked by dos
	 * when the process finishes */
    homedir = ZERO;

	IDebug->AddDebugHook((struct Task *)debug_data.current_process, &debug_hook);

    inferior_ptid = pid_to_ptid ((int)debug_data.current_process);
    dprintf("inferior_ptid=%p\n",inferior_ptid);
    add_thread(inferior_ptid);

    /* FIXME: This is from the gdb source: You should call clear_proceed_status before calling proceed.  */
    proceed ((CORE_ADDR) -1, TARGET_SIGNAL_0, 0);
    inferior_created = TRUE;
  
    FUNCX;
}

void
amigaos_kill_inferior (void)
{
//printf("DEBUG: amigaos_kill_inferior()\n");

    FUNC;
  
    if (inferior_created && debug_data.current_process)
    {
		dprintf("Killing %p\n", debug_data.current_process);

/* FIXME: do not use RemTask on a Process!!! */

		IDebug->AddDebugHook(&debug_data.current_process->pr_Task, NULL);

		IExec->RemTask((struct Task *)debug_data.current_process);
		debug_data.current_process = 0;
     
		inferior_created = FALSE;

		dprintf("unpush target\n");
     
		unpush_target (&amigaos_ops);
    }
  
    FUNCX;
}

static void 
amigaos_resume (ptid_t ptid, int step,  enum target_signal signal)
{
	struct ExceptionContext *context = context_ptr;
	struct Task *me = IExec->FindTask(NULL);
    
    dprintf("resume ptid = %08x, step = %d, signal = %d, process = %p\n",
			PIDGET(ptid), step, signal, debug_data.current_process);	

    if (0)   ///(context->Traptype != 0)
    {
			printf("not resuming, signal pending (%lx)\n", context->Traptype);
			FUNCX;
			return;
    }

#if 0
    if (step)
    {
		/* Set single-step */
		context->msr |= MSR_TRACE_ENABLE;
		dprintf("Single step\n");
    }
    else
    {
		dprintf("No single step\n");
		context->msr &= ~MSR_TRACE_ENABLE;
    }
#endif
    dprintf("RestartTask(%p) at pc %08lx\n", debug_data.current_process, context->ip);
    IExec->RestartTask((struct Task *)debug_data.current_process, 0);
}
 



 
static ptid_t 
amigaos_wait (ptid_t ptid, struct target_waitstatus *status)
{
    struct ExceptionContext *context;
    struct Process *process = (struct Process *)PIDGET(ptid);
    uint32 sigRec;
    struct debugger_message *msg;
  
    FUNC;

    if (process == (struct Process *)0xffffffff)
    {    
		process = debug_data.current_process;
    }
  
    dprintf("wait ptid = %p (%08x), status = %p\n", process, PIDGET(ptid), status);
  
    while (1)
    {
		/* Check if our task is still there */
		/*   if (FALSE == is_process_alive(process))
			 {
			 status->kind = TARGET_WAITKIND_EXITED;
			 status->value.integer = 0;

			 dprintf("Target has exited\n");
			 return pid_to_ptid ((int)process);
			 }*/
    
    	if (debug_data.current_process == NULL)
    	{
			 status->kind = TARGET_WAITKIND_EXITED;
			 status->value.integer = 0;

			 dprintf("Target has exited\n");
			 return pid_to_ptid ((int)process);
    	}

		dprintf("Waiting for message (process=%p)\n",debug_data.current_process);


		/* Wait for any event */
		sigRec = IExec->Wait(SIGBREAKF_CTRL_D|SIGBREAKF_CTRL_C|1<<debug_data.debugger_port->mp_SigBit);

		dprintf("Waking up\n");
    
		/* Check for CTRL-D, and exit if it's been sent */
		if (sigRec & SIGBREAKF_CTRL_D)
		{
			/* Make sure the debugger stops waiting */
			status->kind = TARGET_WAITKIND_EXITED;
			status->value.integer = 0;

			FUNCX;
			return pid_to_ptid ((int)process);
		}
    
		/* Check for CTRL-C, and try to suspend the inferior */
		if (sigRec & SIGBREAKF_CTRL_C)
		{
			IExec->SuspendTask((struct Task *)process, 0);
       
			status->kind = TARGET_WAITKIND_STOPPED;
			status->value.sig = TARGET_SIGNAL_TRAP;
       
			FUNCX;
			return pid_to_ptid ((int)process);
		}
     
		while ((msg = (struct debugger_message *)IExec->GetMsg(debug_data.debugger_port)))
		{
			//context = (struct ExceptionContext *)/*FIXME: msg->*/((struct ETask *)process->pr_Task.tc_ETask)->Context;
   			context = context_ptr;
			
			dprintf("Got a signal %d (%s) from process %p @ ip %08lx (ctx=%08lx, msg=%08lx)\n", 
					trap_to_signal(context, msg->flags), 
					target_signal_to_name (trap_to_signal(context, msg->flags)),
					process, context->ip, context, msg);
	
			if (msg->signal != -1)
			{
				/* Got a "signal"... */
				status->value.sig = msg->signal;  //trap_to_signal(context, msg->flags);
				int i = status->value.sig;

				switch (i)
				{
					case TARGET_SIGNAL_CHLD:

						/* Make sure the debugger stops waiting */
						//printf("                                          received CHLD signal\n");
						status->kind = TARGET_WAITKIND_SIGNALLED;
						status->value.integer = 0;

//						FUNCX;
//						return pid_to_ptid ((int)process);
						break;

					case TARGET_SIGNAL_QUIT:

						//printf("                                           Inferior has died(QUIT)\n");
						status->kind = TARGET_WAITKIND_SIGNALLED;
						inferior_created = FALSE;
						debug_data.current_process = 0;
						break;

					case TARGET_SIGNAL_TRAP:
						//printf("                                               TRAP!\n");
						status->kind = TARGET_WAITKIND_STOPPED;
						status->value.sig = TARGET_SIGNAL_TRAP;
						break;

					case TARGET_SIGNAL_SEGV:
					case TARGET_SIGNAL_BUS:
					case TARGET_SIGNAL_INT:
					case TARGET_SIGNAL_FPE:
					case TARGET_SIGNAL_ILL:
					case TARGET_SIGNAL_ALRM:
						//printf("                                               Inferior is stopped\n");
						status->kind = TARGET_WAITKIND_STOPPED;


						break;

					default:
						//printf("                                               Unknown signal (error)\n");
						break;
				}
      
				/* Get rid of the message */
				drop_msg_packet(msg);
	
				/* Clear the "signal" */
				context->Traptype = 0;
	
				FUNCX;
				return pid_to_ptid ((int)process);
			}
      
			/* We get here when we got a message, but it wasn't a real signal. This can happen when
			   a new task is attached, in which case we stop as if we would single step */
	 
			if (msg->flags & TASK_ATTACHED)
			{
				dprintf("New task attach message\n");
				status->kind = TARGET_WAITKIND_STOPPED;
				status->value.sig = TARGET_SIGNAL_TRAP;
			
			    drop_msg_packet(msg);
				FUNCX;          
				return pid_to_ptid ((int)process);
			}
			else if (msg->flags & TASK_OPENLIB)
			{
				/* FIXME: Load symbols here ? */
				dprintf("shared library open\n");
				status->kind = TARGET_WAITKIND_LOADED;
				status->value.sig = 0;
				
				/* Add the library to our internal list */
				if (!amigaos_find_lib(msg->library))
					amigaos_add_lib(msg->library);
				
				drop_msg_packet(msg);
				
				FUNCX;          
				return pid_to_ptid ((int)process);
			}
			else if (msg->flags & TASK_CLOSELIB)
			{
				/* FIXME: Remove library from list */
				//amigaos_rem_lib(amigaos_find_lib(msg->library));
			} else if (msg->flags & TASK_TERMINATED)
			{
				status->kind = TARGET_WAITKIND_SIGNALLED;
				inferior_created = FALSE;
				debug_data.current_process = 0;
			}
			
			/* It wasn't a trap (hence no signal) */
			drop_msg_packet(msg);
		}
    }
    
    FUNCX;
}

static void 
amigaos_fetch_registers (int regno)
{
    int i;
    struct ExceptionContext *context;
    struct gdbarch_tdep *tdep = gdbarch_tdep (current_gdbarch);

    FUNC;
  
  	if (debug_data.current_process)
		context = context_ptr;
	else
		return;

  	dprintf("inferior_ptid=%p\n",inferior_ptid);
    dprintf("regno = %d (%s)\n", regno, REGISTER_NAME(regno));
    dprintf("context = %p, sp = %lx, pc = %lx, lr = %lx\n", context, context->gpr[1], context->ip, context->lr);
  
    if (regno == -1)
    {
		for (i = 0; i < 31; i++)
			regcache_raw_supply(current_regcache, i, (void *)&context->gpr[i]);
     
		for (i = 0; i < 31; i++)
			regcache_raw_supply(current_regcache, 32+i, (void *)&context->fpr[i]);
      
		regcache_raw_supply (current_regcache, PC_REGNUM, (void *) &context->ip);
		regcache_raw_supply (current_regcache, tdep->ppc_ps_regnum, (void *) &context->msr);
		regcache_raw_supply (current_regcache, tdep->ppc_cr_regnum, (void *) &context->cr);
		regcache_raw_supply (current_regcache, tdep->ppc_lr_regnum, (void *) &context->lr);
		regcache_raw_supply (current_regcache, tdep->ppc_ctr_regnum, (void *) &context->ctr);
		regcache_raw_supply (current_regcache, tdep->ppc_xer_regnum, (void *) &context->xer);
		regcache_raw_supply (current_regcache, tdep->ppc_fpscr_regnum, (void *) &context->fpscr);
    }
    else
    {
		if (regno >= 0 && regno <= 31)
			regcache_raw_supply (current_regcache, regno, (void *) &context->gpr[regno]);
		else if (regno >= 32 && regno <= 63)
			regcache_raw_supply (current_regcache, regno, (void *) &context->fpr[regno-32]);
		else if (regno == PC_REGNUM)
			regcache_raw_supply (current_regcache, regno, (void *) &context->ip);
		else if (regno == tdep->ppc_ps_regnum)
			regcache_raw_supply (current_regcache, regno, (void *) &context->msr);
		else if (regno == tdep->ppc_cr_regnum)
			regcache_raw_supply (current_regcache, tdep->ppc_cr_regnum, (void *) &context->cr);
		else if (regno == tdep->ppc_lr_regnum)
			regcache_raw_supply (current_regcache, tdep->ppc_lr_regnum, (void *) &context->lr);
		else if (regno == tdep->ppc_ctr_regnum) 
			regcache_raw_supply (current_regcache, tdep->ppc_ctr_regnum, (void *) &context->ctr);
		else if (regno == tdep->ppc_xer_regnum)
			regcache_raw_supply (current_regcache, tdep->ppc_xer_regnum, (void *) &context->xer);
		else if (regno == tdep->ppc_fpscr_regnum)
			regcache_raw_supply (current_regcache, tdep->ppc_fpscr_regnum, (void *) &context->fpscr);
    }  
}

static void 
amigaos_store_registers (int regno)
{
    int i;

	struct ExceptionContext *context = context_ptr;
    struct gdbarch_tdep *tdep = gdbarch_tdep (current_gdbarch);

    FUNC;
    dprintf("regno = %d (%s)\n", regno, REGISTER_NAME(regno));
 
    if (regno == -1)
    {
		for (i = 0; i < 32; i++)
			regcache_raw_collect(current_regcache, i, (void *) &context->gpr[i]);
		for (i = 0; i < 32; i++)
			regcache_raw_collect(current_regcache, 32+i, (void *) &context->fpr[i]);
	
		regcache_raw_collect (current_regcache, PC_REGNUM, (void *) &context->ip);
		regcache_raw_collect (current_regcache, tdep->ppc_ps_regnum, (void *) &context->msr);
		regcache_raw_collect (current_regcache, tdep->ppc_cr_regnum, (void *) &context->cr);
		regcache_raw_collect (current_regcache, tdep->ppc_lr_regnum, (void *) &context->lr);
		regcache_raw_collect (current_regcache, tdep->ppc_ctr_regnum, (void *) &context->ctr);
		regcache_raw_collect (current_regcache, tdep->ppc_xer_regnum, (void *) &context->xer);
		regcache_raw_collect (current_regcache, tdep->ppc_fpscr_regnum, (void *) &context->fpscr);
    }
    else
    {
		if (regno >= 0 && regno <= 31)    
			regcache_raw_collect(current_regcache, regno, (void *) &context->gpr[regno]);
		else if (regno >= 32 && regno <= 63)
			regcache_raw_collect(current_regcache, regno, (void *) &context->fpr[regno-32]);
		else if (regno == PC_REGNUM)
			regcache_raw_collect (current_regcache, PC_REGNUM, (void *) &context->ip);
		else if (regno == tdep->ppc_ps_regnum)
			regcache_raw_collect (current_regcache, tdep->ppc_ps_regnum, (void *) &context->msr);
		else if (regno == tdep->ppc_cr_regnum)
			regcache_raw_collect (current_regcache, tdep->ppc_cr_regnum, (void *) &context->cr);
		else if (regno == tdep->ppc_lr_regnum)
			regcache_raw_collect (current_regcache, tdep->ppc_lr_regnum, (void *) &context->lr);
		else if (regno == tdep->ppc_ctr_regnum)  
			regcache_raw_collect (current_regcache, tdep->ppc_ctr_regnum, (void *) &context->ctr);
		else if (regno == tdep->ppc_xer_regnum)
			regcache_raw_collect (current_regcache, tdep->ppc_xer_regnum, (void *) &context->xer);
		else if (regno == tdep->ppc_fpscr_regnum)
			regcache_raw_collect (current_regcache, tdep->ppc_fpscr_regnum, (void *) &context->fpscr);
    }
  
    FUNCX;
}

static void 
amigaos_prepare_to_store (void)
{
    FUNC; 
    FUNCX;
}

static int 
amigaos_xfer_memory (CORE_ADDR memaddr, char *myaddr, int len,
					 int write,
					 struct mem_attrib *attrib,
					 struct target_ops *target)
{
    dprintf("amigaos_xfer_memory(memaddr = %p, myaddr = %p, len = %d, write = %d, attrib = %p, target = %p)\n",
			(void*)memaddr, myaddr, len, write, attrib, target);
	
    if (write)
    {
    	dprintf("Writing %p to %p (was %p)\n",*(uint32*)myaddr,memaddr,*(void**)memaddr);
		memcpy((void*)memaddr, (void*)myaddr, len);
		IExec->CacheClearE((void*)memaddr, len, CACRF_ClearI);
		dprintf("Now is %p\n",*(void**)memaddr);
    }
    else
    {
		memcpy((void*)myaddr, (void*)memaddr, len);
    }	

    return len;
}


static void 
amigaos_files_info (struct target_ops *target)
{
    printf_unfiltered ("Debugging process %p\n", 
					   debug_data.current_process);
}
 
static void 
amigaos_terminal_init (void)
{
	dprintf("terminal_init (STUB)\n");
}

static void 
amigaos_terminal_inferior (void)
{
	dprintf("terminal_inferior is a STUB\n");
}

static void 
amigaos_terminal_ours (void)
{
	dprintf("terminal_ours is a STUB\n");
}


static void
amigaos_terminal_info (char *args, int from_tty)
{
    FUNC;

    printf_unfiltered("Yes, we have a terminal (STUB)\n");

    FUNCX;
}


static void 
amigaos_mourn_inferior (void)
{
    FUNC;
 
    unpush_target(&amigaos_ops);
    generic_mourn_inferior();
  
    FUNCX;
}


static void 
amigaos_stop (void)
{
    FUNC;
  
    normal_stop ();
    inferior_ptid = null_ptid;
  
    FUNCX;
}

int 
amigaos_memory_insert_breakpoint(CORE_ADDR addr, char *contents_cache)
{
  int val;
  const unsigned char *bp;
  int bplen;
  uint32 oldAttr;
  APTR stack;
  CORE_ADDR host_addr;

  /* Relocate the address manually if it elf related */
  if (addr >= code_elf_addr && addr < code_elf_addr + code_size)
	  host_addr = (CORE_ADDR)((char*)addr - (char*)code_elf_addr + (char*)code_relocated_addr);
  else
	  host_addr = addr;

  dprintf("Trying to set breakpoint at %p (host_addr=%p, code_elf_addr=%p, code_size=%p)\n", addr, host_addr, code_elf_addr,(void*)code_size);
  
  /* Determine appropriate breakpoint contents and size for this address.  */
  bp = BREAKPOINT_FROM_PC (&addr, &bplen);
  if (bp == NULL)
    error ("Software breakpoints not implemented for this target.");

  addr = (CORE_ADDR)host_addr;

  /* Save the memory contents.  */
  val = target_read_memory (addr, contents_cache, bplen);

  dprintf("Saved at addr %p the instruction %p\n",(void*)addr,*(void **)contents_cache);

  /* Write the breakpoint.  */
  if (val == 0)
  {
  	/* Go supervisor */
	stack = IExec->SuperState();
	
	dprintf("Setting breakpoint at addr=%p bp=%p\n", addr, bp);
  	/* Make sure to unprotect the memory area */
	oldAttr = IMMU->GetMemoryAttrs((APTR)addr, 0);
	IMMU->SetMemoryAttrs((APTR)addr, bplen, MEMATTRF_READ_WRITE);
	
    val = target_write_memory (addr, (char *) bp, bplen);
	
	/* Set old attributes again */
	IMMU->SetMemoryAttrs((APTR)addr, bplen, oldAttr);
	
	/* Return to old state */
	if (stack)
		IExec->UserState(stack);
  }

  return val;
}


int 
amigaos_memory_remove_breakpoint(CORE_ADDR addr, char *contents_cache)
{
  const unsigned char *bp;
  int bplen;
  uint32 oldAttr;
  APTR stack;
  int val;

  CORE_ADDR host_addr;

  /* Relocate the address manually if it elf related */
  if (addr >= code_elf_addr && addr < code_elf_addr + code_size)
	  host_addr = (CORE_ADDR)((char*)addr - (char*)code_elf_addr + (char*)code_relocated_addr);
  else
	  host_addr = addr;

  dprintf("Trying to remove breakpoint at %p (host_addr=%p, code_elf_addr=%p, code_size=%p)\n", addr, host_addr, code_elf_addr,(void*)code_size);

  /* Determine appropriate breakpoint contents and size for this address.  */
  bp = BREAKPOINT_FROM_PC (&addr, &bplen);
  if (bp == NULL)
    error ("Software breakpoints not implemented for this target.");

  addr = (CORE_ADDR)host_addr;

  /* Go supervisor */
  stack = IExec->SuperState();
	
  dprintf("Clearing breakpoint at %p, i.e., restoring with instruction %p\n", addr,*(void**)contents_cache);
  
  /* Make sure to unprotect the memory area */
  oldAttr = IMMU->GetMemoryAttrs((APTR)addr, 0);
  IMMU->SetMemoryAttrs((APTR)addr, bplen, MEMATTRF_READ_WRITE);
	
  val = target_write_memory (addr, contents_cache, bplen);
  
  /* Set old attributes again */
  IMMU->SetMemoryAttrs((APTR)addr, bplen, oldAttr);
	
  /* Return to old state */
  if (stack)
	IExec->UserState(stack);

  return val;
}



static void
init_amigaos_ops (void)
{
//printf("DEBUG: init_amigaos_ops()\n");

    amigaos_ops.to_shortname = "subtask";
    amigaos_ops.to_longname = "AmigaOS 4 target process";
    amigaos_ops.to_doc = "Debug a Task/Process running on AmigaOS 4\n"
		"Use \"target subtask <process_id>\" to attach";
    amigaos_ops.to_open = amigaos_open;
    amigaos_ops.to_close = amigaos_close;
    amigaos_ops.to_attach = amigaos_attach;
    amigaos_ops.to_detach = amigaos_detach;
    amigaos_ops.to_resume = amigaos_resume;
    amigaos_ops.to_wait = amigaos_wait;
/**/amigaos_ops.to_fetch_registers = amigaos_fetch_registers;
/**/amigaos_ops.to_store_registers = amigaos_store_registers;
/**/amigaos_ops.to_prepare_to_store = amigaos_prepare_to_store;
/* FIXME use to_xfer_partial instead of deprecated_xfer_memory */
/**/amigaos_ops.deprecated_xfer_memory = amigaos_xfer_memory;
/**/amigaos_ops.to_files_info = amigaos_files_info;
/**/amigaos_ops.to_insert_breakpoint = amigaos_memory_insert_breakpoint;
/**/amigaos_ops.to_remove_breakpoint = amigaos_memory_remove_breakpoint;
    amigaos_ops.to_terminal_init = amigaos_terminal_init;
    amigaos_ops.to_terminal_inferior = amigaos_terminal_inferior;
    amigaos_ops.to_terminal_ours_for_output = amigaos_terminal_ours;
    amigaos_ops.to_terminal_ours = amigaos_terminal_ours;
    amigaos_ops.to_terminal_info = amigaos_terminal_info;
/**/amigaos_ops.to_kill = amigaos_kill_inferior;
/**/amigaos_ops.to_create_inferior = amigaos_create_inferior;
    amigaos_ops.to_mourn_inferior = amigaos_mourn_inferior;
/**/amigaos_ops.to_can_run = amigaos_can_run;
    amigaos_ops.to_stop = amigaos_stop;
    amigaos_ops.to_pid_to_exec_file = amigaos_pid_to_exec_file;
    
    amigaos_ops.to_stratum = process_stratum;
    amigaos_ops.to_has_all_memory = 1;
    amigaos_ops.to_has_memory = 1;
    amigaos_ops.to_has_stack = 1;
    amigaos_ops.to_has_registers = 1;
    amigaos_ops.to_has_execution = 1;
    amigaos_ops.to_magic = OPS_MAGIC;

}


void
_initialize_amigaos_nat (void)
{
//printf("DEBUG: _initialize_amigaos_nat()\n");

    init_amigaos_ops();
    add_target(&amigaos_ops);
    amigaos_solib_init();
}
