/*
 * Copyright (c) 2010 by Cristian Maglie <c.maglie@arduino.cc>
 * Copyright (c) 2014 by Paul Stoffregen <paul@pjrc.com> (Transaction API)
 * Copyright (c) 2014 by Matthijs Kooijman <matthijs@stdin.nl> (SPISettings AVR)
 * Copyright (c) 2014 by Andrew J. Kroll <xxxajk@gmail.com> (atomicity fixes)
 * Copyright (c) 2018 by Bryan Craker of Alorium Technology <info@aloriumtech.com> (Support for addressibility for SPI XBs)
 * SPI Master library for arduino.
 *
 * This file is free software; you can redistribute it and/or modify
 * it under the terms of either the GNU General Public License version 2
 * or the GNU Lesser General Public License version 2.1, both as
 * published by the Free Software Foundation.
 */

#ifndef _XLR8_SPI_H_INCLUDED
#define _XLR8_SPI_H_INCLUDED

#include <Arduino.h>

// XLR8_SPI_HAS_TRANSACTION means SPI has beginTransaction(), endTransaction(),
// usingInterrupt(), and SPISetting(clock, bitOrder, dataMode)
#define XLR8_SPI_HAS_TRANSACTION 1

// XLR8_SPI_HAS_NOTUSINGINTERRUPT means that SPI has notUsingInterrupt() method
#define XLR8_SPI_HAS_NOTUSINGINTERRUPT 1

// XLR8_SPI_ATOMIC_VERSION means that SPI has atomicity fixes and what version.
// This way when there is a bug fix you can check this define to alert users
// of your code if it uses better version of this library.
// This also implies everything that XLR8_SPI_HAS_TRANSACTION as documented above is
// available too.
#define XLR8_SPI_ATOMIC_VERSION 1

// Uncomment this line to add detection of mismatched begin/end transactions.
// A mismatch occurs if other libraries fail to use SPI.endTransaction() for
// each SPI.beginTransaction().  Connect an LED to this pin.  The LED will turn
// on if any mismatch is ever detected.
//#define XLR8_SPI_TRANSACTION_MISMATCH_LED 5

#ifndef LSBFIRST
#define LSBFIRST 0
#endif
#ifndef MSBFIRST
#define MSBFIRST 1
#endif

#define XLR8_SPI_CLOCK_DIV4 0x00
#define XLR8_SPI_CLOCK_DIV16 0x01
#define XLR8_SPI_CLOCK_DIV64 0x02
#define XLR8_SPI_CLOCK_DIV128 0x03
#define XLR8_SPI_CLOCK_DIV2 0x04
#define XLR8_SPI_CLOCK_DIV8 0x05
#define XLR8_SPI_CLOCK_DIV32 0x06

#define XLR8_SPI_MODE0 0x00
#define XLR8_SPI_MODE1 0x04
#define XLR8_SPI_MODE2 0x08
#define XLR8_SPI_MODE3 0x0C

#define XLR8_SPI_MODE_MASK 0x0C  // CPOL = bit 3, CPHA = bit 2 on SPCR
#define XLR8_SPI_CLOCK_MASK 0x03  // SPR1 = bit 1, SPR0 = bit 0 on SPCR
#define XLR8_SPI_2XCLOCK_MASK 0x01  // SPI2X = bit 0 on SPSR

// define XLR8_SPI_AVR_EIMSK for AVR boards with external interrupt pins
#if defined(EIMSK)
  #define XLR8_SPI_AVR_EIMSK  EIMSK
#elif defined(GICR)
  #define XLR8_SPI_AVR_EIMSK  GICR
#elif defined(GIMSK)
  #define XLR8_SPI_AVR_EIMSK  GIMSK
#endif

class XLR8SPISettings {
public:
  XLR8SPISettings(uint32_t clock, uint8_t bitOrder, uint8_t dataMode) {
    if (__builtin_constant_p(clock)) {
      init_AlwaysInline(clock, bitOrder, dataMode);
    } else {
      init_MightInline(clock, bitOrder, dataMode);
    }
  }
  XLR8SPISettings() {
    init_AlwaysInline(4000000, MSBFIRST, XLR8_SPI_MODE0);
  }
private:
  void init_MightInline(uint32_t clock, uint8_t bitOrder, uint8_t dataMode) {
    init_AlwaysInline(clock, bitOrder, dataMode);
  }
  void init_AlwaysInline(uint32_t clock, uint8_t bitOrder, uint8_t dataMode)
    __attribute__((__always_inline__)) {
    // Clock settings are defined as follows. Note that this shows SPI2X
    // inverted, so the bits form increasing numbers. Also note that
    // fosc/64 appears twice
    // SPR1 SPR0 ~SPI2X Freq
    //   0    0     0   fosc/2
    //   0    0     1   fosc/4
    //   0    1     0   fosc/8
    //   0    1     1   fosc/16
    //   1    0     0   fosc/32
    //   1    0     1   fosc/64
    //   1    1     0   fosc/64
    //   1    1     1   fosc/128

    // We find the fastest clock that is less than or equal to the
    // given clock rate. The clock divider that results in clock_setting
    // is 2 ^^ (clock_div + 1). If nothing is slow enough, we'll use the
    // slowest (128 == 2 ^^ 7, so clock_div = 6).
    uint8_t clockDiv;

    // When the clock is known at compiletime, use this if-then-else
    // cascade, which the compiler knows how to completely optimize
    // away. When clock is not known, use a loop instead, which generates
    // shorter code.
    if (__builtin_constant_p(clock)) {
      if (clock >= F_CPU / 2) {
        clockDiv = 0;
      } else if (clock >= F_CPU / 4) {
        clockDiv = 1;
      } else if (clock >= F_CPU / 8) {
        clockDiv = 2;
      } else if (clock >= F_CPU / 16) {
        clockDiv = 3;
      } else if (clock >= F_CPU / 32) {
        clockDiv = 4;
      } else if (clock >= F_CPU / 64) {
        clockDiv = 5;
      } else {
        clockDiv = 6;
      }
    } else {
      uint32_t clockSetting = F_CPU / 2;
      clockDiv = 0;
      while (clockDiv < 6 && clock < clockSetting) {
        clockSetting /= 2;
        clockDiv++;
      }
    }

    // Compensate for the duplicate fosc/64
    if (clockDiv == 6)
    clockDiv = 7;

    // Invert the SPI2X bit
    clockDiv ^= 0x1;

    // Pack into the XLR8SPISettings class
    spcr = _BV(SPE) | _BV(MSTR) | ((bitOrder == LSBFIRST) ? _BV(DORD) : 0) |
      (dataMode & XLR8_SPI_MODE_MASK) | ((clockDiv >> 1) & XLR8_SPI_CLOCK_MASK);
    spsr = clockDiv & XLR8_SPI_2XCLOCK_MASK;
  }
  uint8_t spcr;
  uint8_t spsr;
  friend class XLR8SPIClass;
};


class XLR8SPIClass {
public:

  inline XLR8SPIClass() {
    // Default constructor, will result in the default Arduino hardware SPI
  }

  inline XLR8SPIClass(uint8_t SPCR_addr, uint8_t SPSR_addr, uint8_t SPDR_addr) {
    spcrReg = (volatile uint8_t *)SPCR_addr;
    spsrReg = (volatile uint8_t *)SPSR_addr;
    spdrReg = (volatile uint8_t *)SPDR_addr;
  }

  // If the SPI interface uses a builtin device or GPIO, don't 
  // interact with Arduino pins, they have to be handled outside the 
  // library.
  inline void skipArduinoPins() {
    useArduinoPins = false;
  }

  // Initialize the SPI library
  void begin();

  // If SPI is used from within an interrupt, this function registers
  // that interrupt with the SPI library, so beginTransaction() can
  // prevent conflicts.  The input interruptNumber is the number used
  // with attachInterrupt.  If SPI is used from a different interrupt
  // (eg, a timer), interruptNumber should be 255.
  void usingInterrupt(uint8_t interruptNumber);
  // And this does the opposite.
  void notUsingInterrupt(uint8_t interruptNumber);
  // Note: the usingInterrupt and notUsingInterrupt functions should
  // not to be called from ISR context or inside a transaction.
  // For details see:
  // https://github.com/arduino/Arduino/pull/2381
  // https://github.com/arduino/Arduino/pull/2449

  // Before using SPI.transfer() or asserting chip select pins,
  // this function is used to gain exclusive access to the SPI bus
  // and configure the correct settings.
  inline void beginTransaction(XLR8SPISettings settings) {
    if (interruptMode > 0) {
      uint8_t sreg = SREG;
      noInterrupts();

      #ifdef XLR8_SPI_AVR_EIMSK
      if (interruptMode == 1) {
        interruptSave = XLR8_SPI_AVR_EIMSK;
        XLR8_SPI_AVR_EIMSK &= ~interruptMask;
        SREG = sreg;
      } else
      #endif
      {
        interruptSave = sreg;
      }
    }

    #ifdef XLR8_SPI_TRANSACTION_MISMATCH_LED
    if (inTransactionFlag) {
      pinMode(XLR8_SPI_TRANSACTION_MISMATCH_LED, OUTPUT);
      digitalWrite(XLR8_SPI_TRANSACTION_MISMATCH_LED, HIGH);
    }
    inTransactionFlag = 1;
    #endif

    *spcrReg = settings.spcr;
    *spsrReg = settings.spsr;
  }

  // Write to the SPI bus (MOSI pin) and also receive (MISO pin)
  inline uint8_t transfer(uint8_t data) {
    *spdrReg = data;
    /*
     * The following NOP introduces a small delay that can prevent the wait
     * loop form iterating when running at the maximum speed. This gives
     * about 10% more speed, even if it seems counter-intuitive. At lower
     * speeds it is unnoticed.
     */
    asm volatile("nop");
    while (!(*spsrReg & _BV(SPIF))) ; // wait
    return *spdrReg;
  }
  inline uint16_t transfer16(uint16_t data) {
    union { uint16_t val; struct { uint8_t lsb; uint8_t msb; }; } in, out;
    in.val = data;
    if (!(*spcrReg & _BV(DORD))) {
      *spdrReg = in.msb;
      asm volatile("nop"); // See transfer(uint8_t) function
      while (!(*spsrReg & _BV(SPIF))) ;
      out.msb = *spdrReg;
      *spdrReg = in.lsb;
      asm volatile("nop");
      while (!(*spsrReg & _BV(SPIF))) ;
      out.lsb = *spdrReg;
    } else {
      *spdrReg = in.lsb;
      asm volatile("nop");
      while (!(*spsrReg & _BV(SPIF))) ;
      out.lsb = *spdrReg;
      *spdrReg = in.msb;
      asm volatile("nop");
      while (!(*spsrReg & _BV(SPIF))) ;
      out.msb = *spdrReg;
    }
    return out.val;
  }
  inline void transfer(void *buf, size_t count) {
    if (count == 0) return;
    uint8_t *p = (uint8_t *)buf;
    *spdrReg = *p;
    while (--count > 0) {
      uint8_t out = *(p + 1);
      while (!(*spsrReg & _BV(SPIF))) ;
      uint8_t in = *spdrReg;
      *spdrReg = out;
      *p++ = in;
    }
    while (!(*spsrReg & _BV(SPIF))) ;
    *p = *spdrReg;
  }
  // After performing a group of transfers and releasing the chip select
  // signal, this function allows others to access the SPI bus
  inline void endTransaction(void) {
    #ifdef XLR8_SPI_TRANSACTION_MISMATCH_LED
    if (!inTransactionFlag) {
      pinMode(XLR8_SPI_TRANSACTION_MISMATCH_LED, OUTPUT);
      digitalWrite(XLR8_SPI_TRANSACTION_MISMATCH_LED, HIGH);
    }
    inTransactionFlag = 0;
    #endif

    if (interruptMode > 0) {
      #ifdef XLR8_SPI_AVR_EIMSK
      uint8_t sreg = SREG;
      #endif
      noInterrupts();
      #ifdef XLR8_SPI_AVR_EIMSK
      if (interruptMode == 1) {
        XLR8_SPI_AVR_EIMSK = interruptSave;
        SREG = sreg;
      } else
      #endif
      {
        SREG = interruptSave;
      }
    }
  }

  // Disable the SPI bus
  void end();

  // This function is deprecated.  New applications should use
  // beginTransaction() to configure SPI settings.
  inline void setBitOrder(uint8_t bitOrder) {
    if (bitOrder == LSBFIRST) *spcrReg |= _BV(DORD);
    else *spcrReg &= ~(_BV(DORD));
  }
  // This function is deprecated.  New applications should use
  // beginTransaction() to configure SPI settings.
  inline void setDataMode(uint8_t dataMode) {
    *spcrReg = (*spcrReg & ~XLR8_SPI_MODE_MASK) | dataMode;
  }
  // This function is deprecated.  New applications should use
  // beginTransaction() to configure SPI settings.
  inline void setClockDivider(uint8_t clockDiv) {
    *spcrReg = (*spcrReg & ~XLR8_SPI_CLOCK_MASK) | (clockDiv & XLR8_SPI_CLOCK_MASK);
    *spsrReg = (*spsrReg & ~XLR8_SPI_2XCLOCK_MASK) | ((clockDiv >> 2) & XLR8_SPI_2XCLOCK_MASK);
  }
  // These undocumented functions should not be used.  SPI.transfer()
  // polls the hardware flag which is automatically cleared as the
  // AVR responds to SPI's interrupt
  inline void attachInterrupt() { *spcrReg |= _BV(SPIE); }
  inline void detachInterrupt() { *spcrReg &= ~_BV(SPIE); }

  // Set the pin numbers of SCK, MISO, MOSI, and SS, used if 
  // the SPI XB is set up on Arduino pins.
  inline void setPins(uint8_t sck, uint8_t miso, uint8_t mosi, uint8_t ss) {
    sckPin  = sck;
    misoPin = miso;
    mosiPin = mosi;
    ssPin   = ss;
  }

  // Write to the SPCR register
  inline void writeSPCR(uint8_t data) {
    *spcrReg = data;
  }
  // Read from the SPCR register
  inline uint8_t readSPCR() {
    return *spcrReg;
  }
  // Write to the SPSR register
  inline void writeSPSR(uint8_t data) {
    *spsrReg = data;
  }
  // Read from the SPSR register
  inline uint8_t readSPSR() {
    return *spsrReg;
  }
  // Write to the SPDR register
  inline void writeSPDR(uint8_t data) {
    *spdrReg = data;
  }
  // Read from the SPDR register
  inline uint8_t readSPDR() {
    return *spdrReg;
  }

private:
  volatile uint8_t * spcrReg = (volatile uint8_t *)0x4c;
  volatile uint8_t * spsrReg = (volatile uint8_t *)0x4d;
  volatile uint8_t * spdrReg = (volatile uint8_t *)0x4e;
  bool useArduinoPins = true;
  uint8_t sckPin  = 13;
  uint8_t misoPin = 12;
  uint8_t mosiPin = 11;
  uint8_t ssPin   = 10;
  uint8_t initialized;
  uint8_t interruptMode; // 0=none, 1=mask, 2=global
  uint8_t interruptMask; // which interrupts to mask
  uint8_t interruptSave; // temp storage, to restore state
  #ifdef XLR8_SPI_TRANSACTION_MISMATCH_LED
  uint8_t inTransactionFlag;
  #endif
};

#endif
