/*
 * Based on arch/arm/include/asm/io.h
 *
 * Copyright (C) 1996-2000 Russell King
 * Copyright (C) 2012 ARM Ltd.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 2 as
 * published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
#ifndef __ASM_IO_H
#define __ASM_IO_H

#ifdef __KERNEL__

#include <linux/types.h>
#include <linux/blk_types.h>

#include <asm/byteorder.h>
#include <asm/barrier.h>
#include <asm/memory.h>
#include <asm/pgtable.h>
#include <asm/early_ioremap.h>
#include <asm/alternative.h>
#include <asm/cpufeature.h>

#include <xen/xen.h>

/*
 * Generic IO read/write.  These perform native-endian accesses.
 */
#define __raw_writeb __raw_writeb
static inline void __raw_writeb(u8 val, volatile void __iomem *addr)
{
	asm volatile("strb %w0, [%1]" : : "rZ" (val), "r" (addr));
}

#define __raw_writew __raw_writew
static inline void __raw_writew(u16 val, volatile void __iomem *addr)
{
	asm volatile("strh %w0, [%1]" : : "rZ" (val), "r" (addr));
}

#define __raw_writel __raw_writel
static inline void __raw_writel(u32 val, volatile void __iomem *addr)
{
	asm volatile("str %w0, [%1]" : : "rZ" (val), "r" (addr));
}

#define __raw_writeq __raw_writeq
static inline void __raw_writeq(u64 val, volatile void __iomem *addr)
{
	asm volatile("str %x0, [%1]" : : "rZ" (val), "r" (addr));
}

#define __raw_readb __raw_readb
static inline u8 __raw_readb(const volatile void __iomem *addr)
{
	u8 val;
	asm volatile(ALTERNATIVE("ldrb %w0, [%1]",
				 "ldarb %w0, [%1]",
				 ARM64_WORKAROUND_DEVICE_LOAD_ACQUIRE)
		     : "=r" (val) : "r" (addr));
	return val;
}

#define __raw_readw __raw_readw
static inline u16 __raw_readw(const volatile void __iomem *addr)
{
	u16 val;

	asm volatile(ALTERNATIVE("ldrh %w0, [%1]",
				 "ldarh %w0, [%1]",
				 ARM64_WORKAROUND_DEVICE_LOAD_ACQUIRE)
		     : "=r" (val) : "r" (addr));
	return val;
}

#define __raw_readl __raw_readl
static inline u32 __raw_readl(const volatile void __iomem *addr)
{
	u32 val;
	asm volatile(ALTERNATIVE("ldr %w0, [%1]",
				 "ldar %w0, [%1]",
				 ARM64_WORKAROUND_DEVICE_LOAD_ACQUIRE)
		     : "=r" (val) : "r" (addr));
	return val;
}

#define __raw_readq __raw_readq
static inline u64 __raw_readq(const volatile void __iomem *addr)
{
	u64 val;
	asm volatile(ALTERNATIVE("ldr %0, [%1]",
				 "ldar %0, [%1]",
				 ARM64_WORKAROUND_DEVICE_LOAD_ACQUIRE)
		     : "=r" (val) : "r" (addr));
	return val;
}

/* IO barriers */
#define __iormb()		rmb()
#define __iowmb()		wmb()

#define mmiowb()		do { } while (0)

/*
 * Relaxed I/O memory access primitives. These follow the Device memory
 * ordering rules but do not guarantee any ordering relative to Normal memory
 * accesses.
 */
#define readb_relaxed(c)	({ u8  __r = __raw_readb(c); __r; })
#define readw_relaxed(c)	({ u16 __r = le16_to_cpu((__force __le16)__raw_readw(c)); __r; })
#define readl_relaxed(c)	({ u32 __r = le32_to_cpu((__force __le32)__raw_readl(c)); __r; })
#define readq_relaxed(c)	({ u64 __r = le64_to_cpu((__force __le64)__raw_readq(c)); __r; })

#define writeb_relaxed(v,c)	((void)__raw_writeb((v),(c)))
#define writew_relaxed(v,c)	((void)__raw_writew((__force u16)cpu_to_le16(v),(c)))
#define writel_relaxed(v,c)	((void)__raw_writel((__force u32)cpu_to_le32(v),(c)))
#define writeq_relaxed(v,c)	((void)__raw_writeq((__force u64)cpu_to_le64(v),(c)))

/*
 * I/O memory access primitives. Reads are ordered relative to any
 * following Normal memory access. Writes are ordered relative to any prior
 * Normal memory access.
 */
#define readb(c)		({ u8  __v = readb_relaxed(c); __iormb(); __v; })
#define readw(c)		({ u16 __v = readw_relaxed(c); __iormb(); __v; })
#define readl(c)		({ u32 __v = readl_relaxed(c); __iormb(); __v; })
#define readq(c)		({ u64 __v = readq_relaxed(c); __iormb(); __v; })

#define writeb(v,c)		({ __iowmb(); writeb_relaxed((v),(c)); })
#define writew(v,c)		({ __iowmb(); writew_relaxed((v),(c)); })
#define writel(v,c)		({ __iowmb(); writel_relaxed((v),(c)); })
#define writeq(v,c)		({ __iowmb(); writeq_relaxed((v),(c)); })

/*
 *  I/O port access primitives.
 */
#define arch_has_dev_port()	(1)
#define IO_SPACE_LIMIT		(PCI_IO_SIZE - 1)
#define PCI_IOBASE		((void __iomem *)PCI_IO_START)

/*
 * String version of I/O memory access operations.
 */
extern void __memcpy_fromio(void *, const volatile void __iomem *, size_t);
extern void __memcpy_toio(volatile void __iomem *, const void *, size_t);
extern void __memset_io(volatile void __iomem *, int, size_t);

#define memset_io(c,v,l)	__memset_io((c),(v),(l))
#define memcpy_fromio(a,c,l)	__memcpy_fromio((a),(c),(l))
#define memcpy_toio(c,a,l)	__memcpy_toio((c),(a),(l))

/*
 * I/O memory mapping functions.
 */
extern void __iomem *__ioremap(phys_addr_t phys_addr, size_t size, pgprot_t prot);
extern void __iounmap(volatile void __iomem *addr);
extern void __iomem *ioremap_cache(phys_addr_t phys_addr, size_t size);

#define ioremap(addr, size)		__ioremap((addr), (size), __pgprot(PROT_DEVICE_nGnRE))
#define ioremap_nocache(addr, size)	__ioremap((addr), (size), __pgprot(PROT_DEVICE_nGnRE))
#define ioremap_wc(addr, size)		__ioremap((addr), (size), __pgprot(PROT_NORMAL_NC))
#define ioremap_wt(addr, size)		__ioremap((addr), (size), __pgprot(PROT_DEVICE_nGnRE))
#define iounmap				__iounmap

/*
 * io{read,write}{16,32,64}be() macros
 */
#define ioread16be(p)		({ __u16 __v = be16_to_cpu((__force __be16)__raw_readw(p)); __iormb(); __v; })
#define ioread32be(p)		({ __u32 __v = be32_to_cpu((__force __be32)__raw_readl(p)); __iormb(); __v; })
#define ioread64be(p)		({ __u64 __v = be64_to_cpu((__force __be64)__raw_readq(p)); __iormb(); __v; })

#define iowrite16be(v,p)	({ __iowmb(); __raw_writew((__force __u16)cpu_to_be16(v), p); })
#define iowrite32be(v,p)	({ __iowmb(); __raw_writel((__force __u32)cpu_to_be32(v), p); })
#define iowrite64be(v,p)	({ __iowmb(); __raw_writeq((__force __u64)cpu_to_be64(v), p); })



/*
 * io{read,write}{16,32,64}() macros
 */
#define ioread16(p) ioread16be(p)
#define ioread32(p) ioread32be(p)
#define ioread64(p) ioread64be(p)

#define iowrite16(v,p)	iowrite16be(v,p)
#define iowrite32(v,p)	iowrite32be(v,p)
#define iowrite64(v,p)	iowrite64be(v,p)

//#include <asm-generic/io.h>

/*
 * More restrictive address range checking than the default implementation
 * (PHYS_OFFSET and PHYS_MASK taken into account).
 */
#define ARCH_HAS_VALID_PHYS_ADDR_RANGE
extern int valid_phys_addr_range(phys_addr_t addr, size_t size);
extern int valid_mmap_phys_addr_range(unsigned long pfn, size_t size);

extern int devmem_is_allowed(unsigned long pfn);

struct bio_vec;
extern bool xen_biovec_phys_mergeable(const struct bio_vec *vec1,
				      const struct bio_vec *vec2);
#define BIOVEC_PHYS_MERGEABLE(vec1, vec2)				\
	(__BIOVEC_PHYS_MERGEABLE(vec1, vec2) &&				\
	 (!xen_domain() || xen_biovec_phys_mergeable(vec1, vec2)))



/********************************************/

// Mem changes //

/*
 * Convert a physical pointer to a virtual kernel pointer for /dev/mem
 * access
 */
#define xlate_dev_mem_ptr(p)    __va(p)

/*
 * Convert a virtual cached pointer to an uncached pointer
 */
#define xlate_dev_kmem_ptr(p)   p



// Arch changes //

struct pci_dev;

#define pci_iounmap pci_iounmap
extern void pci_iounmap(struct pci_dev *dev, void __iomem *addr);


/*
 * A typesafe __io() helper
 */
static inline void __iomem *__typesafe_io(unsigned long addr)
{
        return (void __iomem *)addr;
}

#define __io(a)         __typesafe_io((a))

#define inb_p           inb
#define inw_p           inw
#define inl_p           inl
#define outb_p          outb
#define outw_p          outw
#define outl_p          outl


#define outb(v,p)       ({ __iowmb(); __raw_writeb(v,__io(p)); })
#define outw(v,p)       ({ __iowmb(); __raw_writew((__force __u16) \
                                        cpu_to_le16(v),__io(p)); })
#define outl(v,p)       ({ __iowmb(); __raw_writel((__force __u32) \
                                        cpu_to_le32(v),__io(p)); })

#define inb(p)  ({ __u8 __v = __raw_readb(__io(p)); __iormb(); __v; })
#define inw(p)  ({ __u16 __v = le16_to_cpu((__force __le16) \
                        __raw_readw(__io(p))); __iormb(); __v; })
#define inl(p)  ({ __u32 __v = le32_to_cpu((__force __le32) \
                        __raw_readl(__io(p))); __iormb(); __v; })



/*
 * {read,write}s{b,w,l,q}() repeatedly access the same memory address in
 * native endianness in 8-, 16-, 32- or 64-bit chunks (@count times).
 */

static inline void readsb(const volatile void __iomem *addr, void *buffer,
                          unsigned int count)
{
        if (count) {
                u8 *buf = buffer;

                do {
                        u8 x = __raw_readb(addr);
                        *buf++ = x;
                } while (--count);
        }
}

static inline void readsw(const volatile void __iomem *addr, void *buffer,
                          unsigned int count)
{
        if (count) {
                u16 *buf = buffer;

                do {
                        u16 x = __raw_readw(addr);
                        *buf++ = x;
                } while (--count);
        }
}

static inline void readsl(const volatile void __iomem *addr, void *buffer,
                          unsigned int count)
{
        if (count) {
                u32 *buf = buffer;

                do {
                        u32 x = __raw_readl(addr);
                        *buf++ = x;
                } while (--count);
        }
}

static inline void readsq(const volatile void __iomem *addr, void *buffer,
                          unsigned int count)
{
        if (count) {
                u64 *buf = buffer;

                do {
                        u64 x = __raw_readq(addr);
                        *buf++ = x;
                } while (--count);
        }
}

static inline void writesb(volatile void __iomem *addr, const void *buffer,
                           unsigned int count)
{
        if (count) {
                const u8 *buf = buffer;

                do {
                        __raw_writeb(*buf++, addr);
                } while (--count);
        }
}

static inline void writesw(volatile void __iomem *addr, const void *buffer,
                           unsigned int count)
{
        if (count) {
                const u16 *buf = buffer;

                do {
                        __raw_writew(*buf++, addr);
                } while (--count);
        }
}


static inline void writesl(volatile void __iomem *addr, const void *buffer,
                           unsigned int count)
{
        if (count) {
                const u32 *buf = buffer;

                do {
                        __raw_writel(*buf++, addr);
                } while (--count);
        }
}

static inline void writesq(volatile void __iomem *addr, const void *buffer,
                           unsigned int count)
{
        if (count) {
                const u64 *buf = buffer;

                do {
                        __raw_writeq(*buf++, addr);
                } while (--count);
        }
}



////// in or read


static inline void insb(unsigned long addr, void *buffer, unsigned int count)
{
        readsb(PCI_IOBASE + addr, buffer, count);
}

static inline void insw(unsigned long addr, void *buffer, unsigned int count)
{
        readsw(PCI_IOBASE + addr, buffer, count);
}


static inline void insl(unsigned long addr, void *buffer, unsigned int count)
{
        readsl(PCI_IOBASE + addr, buffer, count);
}


////// out or write

static inline void outsb(unsigned long addr, const void *buffer,
                         unsigned int count)
{
        writesb(PCI_IOBASE + addr, buffer, count);
}

static inline void outsw(unsigned long addr, const void *buffer,
                         unsigned int count)
{
        writesw(PCI_IOBASE + addr, buffer, count);
}

static inline void outsl(unsigned long addr, const void *buffer,
                         unsigned int count)
{
        writesl(PCI_IOBASE + addr, buffer, count);
}

/*******************************************/


#endif	/* __KERNEL__ */
#endif	/* __ASM_IO_H */
