///////////////////////////////////////////////////////////////////
//=================================================================
//  Copyright(c) Superion Technology Group Inc., 2015
//  ALL RIGHTS RESERVED
//  $Id: avr_spi_pkg.svh 1170 2016-03-14 16:42:34Z matt $
//=================================================================
//
// File name:  : avr_spi_pkg.svh
// Author      : Greg Lund
// Description : AVR SPI module pacakge
//=================================================================
///////////////////////////////////////////////////////////////////
`ifndef _AVR_SPI_PKG
 `define _AVR_SPI_PKG


package avr_spi_pkg;

 `include "bit_def_pack.vh"

  // Registers
  typedef  struct packed {
    logic         spie; // interrupt enable
    logic         spe;  // eanble SPI functionality
    logic         dord; // data order.  1 = LSB first, 0 = MSB first
    logic         mstr; // im a master
    logic         cpol; // clock polarity
    logic         cpha; // clock phase
    logic [1:0]   spr;        // master clock divider select
  } spcr_t;

  function spcr_t dbus2spcr(input logic [7:0] a);
    return {a[SPIE_bit],
            a[SPE_bit],
            a[DORD_bit],
            a[MSTR_bit],
            a[CPOL_bit],
            a[CPHA_bit],
            a[SPR1_bit],
            a[SPR0_bit]};
  endfunction: dbus2spcr


  function [7:0] spcr2dbus (input spcr_t a);
    logic [7:0]   tmp;
    tmp[SPIE_bit] = a.spie;
    tmp[SPE_bit] = a.spe;
    tmp[DORD_bit] = a.dord;
    tmp[MSTR_bit] = a.mstr;
    tmp[CPOL_bit] = a.cpol;
    tmp[CPHA_bit] = a.cpha;
    tmp[SPR1_bit] = a.spr[1];
    tmp[SPR0_bit] = a.spr[0];
    return  tmp;
  endfunction // spcr2dbus

endpackage: avr_spi_pkg



`endif
