///////////////////////////////////////////////////////////////////
//=================================================================
//  Copyright(c) Superion Technology Group Inc., 2015
//  ALL RIGHTS RESERVED
//  $Id:  $
//=================================================================
//
// File name:  : avr_spi.v
// Author      : Greg Lund
// Description : AVR SPI module
//  1. NOTE: Fixed bit assignments for SPCR.  See spcr_t typdef below
//=================================================================
///////////////////////////////////////////////////////////////////

// ORIGINAL HEADER
//**********************************************************************************************
// SPI Peripheral for the AVR Core
// Version 1.2
// Modified 10.01.2007
// Designed by Ruslan Lepetenok
// Internal resynchronizers for scki and ss_b inputs were added
//**********************************************************************************************

`include "avr_spi_pkg.svh"

module avr_spi
  #(parameter DESIGN_CONFIG = 9,       // use default image
    parameter SPCR_Address    = 6'h2C, // SPI Control Register
    parameter SPSR_Address    = 6'h2D, // SPI Status Register
    parameter SPDR_Address    = 6'h2E // SPI I/O Data Registerparameter SPCR_Addr,
    )
  (// AVR Control
   input            rst_n,
   input            clk,
   input            clken,

   input [5:0]      adr,
   input [7:0]      dbus_in,
   output reg [7:0] dbus_out,
   input            iore,
   input            iowe,
   output reg       out_en,


   // SPI i/f
   input logic      clk_scki,

   input            misoi,
   input            mosii,
   input            scki, // Resynch
   input            ss_b, // Resynch
   output reg       misoo,
   output reg       mosio,
   output reg       scko,
   output           spe,
   output           spimaster,

   // SRAM space
   input wire [7:0] ramadr,
   input wire       ramre,
   input wire       ramwe,
   input wire       dm_sel,

   // IRQ
   output           spiirq,
   input            spiack,
   // Slave Programming Mode
   input            por,
   input            spiextload,
   output           spidwrite,
   output           spiload
   );

  /*AUTOLOGIC*/
  // Beginning of automatic wires (for undeclared instantiated-module outputs)
  avr_spi_pkg::spcr_t core_sckd_spcr;         // From u_core of avr_spi_core.v
  logic                 core_sckd_spdr7_fall;   // From u_core of avr_spi_core.v
  logic                 core_sckd_spdr7_rise;   // From u_core of avr_spi_core.v
  logic [7:0]           core_sckd_spdr_sh;      // From u_core of avr_spi_core.v
  logic                 rst_sckd_n;             // From u_rst_gen of avr_spi_sckd_rst_gen.v
  logic [1:0]           sckd_core_mosi_cpt;     // From u_sckd of avr_spi_sckd.v
  logic [1:0]           sckd_core_scki_div2;    // From u_sckd of avr_spi_sckd.v
  // End of automatics
  /*AUTOREGINPUT*/

  avr_spi_core
    #(/*AUTOINSTPARAM*/
      // Parameters
      .DESIGN_CONFIG                    (DESIGN_CONFIG),
      .SPCR_Address                     (SPCR_Address),
      .SPSR_Address                     (SPSR_Address),
      .SPDR_Address                     (SPDR_Address))
    u_core
      (.misoo(),
       /*AUTOINST*/
       // Outputs
       .dbus_out                        (dbus_out[7:0]),
       .out_en                          (out_en),
       .core_sckd_spcr                  (core_sckd_spcr),
       .core_sckd_spdr_sh               (core_sckd_spdr_sh[7:0]),
       .core_sckd_spdr7_rise            (core_sckd_spdr7_rise),
       .core_sckd_spdr7_fall            (core_sckd_spdr7_fall),
       .mosio                           (mosio),
       .scko                            (scko),
       .spe                             (spe),
       .spimaster                       (spimaster),
       .spiirq                          (spiirq),
       .spidwrite                       (spidwrite),
       .spiload                         (spiload),
       // Inputs
       .rst_n                           (rst_n),
       .clk                             (clk),
       .clken                           (clken),
       .adr                             (adr[5:0]),
       .dbus_in                         (dbus_in[7:0]),
       .iore                            (iore),
       .iowe                            (iowe),
       .sckd_core_mosi_cpt              (sckd_core_mosi_cpt[1:0]),
       .sckd_core_scki_div2             (sckd_core_scki_div2[1:0]),
       .misoi                           (misoi),
       .mosii                           (mosii),
       .scki                            (scki),
       .ss_b                            (ss_b),
       .ramadr                          (ramadr[7:0]),
       .ramre                           (ramre),
       .ramwe                           (ramwe),
       .dm_sel                          (dm_sel),
       .spiack                          (spiack),
       .por                             (por),
       .spiextload                      (spiextload));


  avr_spi_sckd
    u_sckd
      (/*AUTOINST*/
       // Outputs
       .sckd_core_mosi_cpt              (sckd_core_mosi_cpt[1:0]),
       .sckd_core_scki_div2             (sckd_core_scki_div2[1:0]),
       .misoo                           (misoo),
       // Inputs
       .clk_scki                        (clk_scki),
       .ss_b                            (ss_b),
       .rst_sckd_n                      (rst_sckd_n),
       .core_sckd_spcr                  (core_sckd_spcr),
       .mosii                           (mosii),
       .core_sckd_spdr_sh               (core_sckd_spdr_sh[7:0]),
       .core_sckd_spdr7_rise            (core_sckd_spdr7_rise),
       .core_sckd_spdr7_fall            (core_sckd_spdr7_fall));


  avr_spi_sckd_rst_gen
    u_rst_gen
      (/*AUTOINST*/
       // Outputs
       .rst_sckd_n                      (rst_sckd_n),
       // Inputs
       .clk_scki                        (clk_scki),
       .ss_b                            (ss_b),
       .rst_n                           (rst_n),
       .core_sckd_spcr                  (core_sckd_spcr));


`ifndef VERILATOR
   
  ERROR_not_spie: assert property
  (@(posedge clk) disable iff (!rst_n)
   !core_sckd_spcr.spe |-> (u_sckd.xfer0_rise && !core_sckd_spdr7_rise && !u_sckd.misoo_cpha0_rise &&
                             u_sckd.xfer0_fall && !core_sckd_spdr7_fall && !u_sckd.misoo_cpha0_fall &&
                             !u_sckd.misoo_cpha1_fall &&
                             !u_sckd.misoo_cpha1_rise));

  ERROR_spie_mstr: assert property
  (@(posedge clk) disable iff (!rst_n)
   (core_sckd_spcr.spe && core_sckd_spcr.mstr) |-> (u_sckd.xfer0_rise && !core_sckd_spdr7_rise && !u_sckd.misoo_cpha0_rise &&
                                                     u_sckd.xfer0_fall && !core_sckd_spdr7_fall && !u_sckd.misoo_cpha0_fall &&
                                                     !u_sckd.misoo_cpha1_fall &&
                                                     !u_sckd.misoo_cpha1_rise));
  ERROR_cpha0_cpol0_toggle: assert property
  (@(posedge clk) disable iff (!rst_n)
   (!core_sckd_spcr.cpha && !core_sckd_spcr.cpol) |-> (u_sckd.xfer0_rise && !core_sckd_spdr7_rise && !u_sckd.misoo_cpha0_rise &&
                                                       !u_sckd.misoo_cpha1_fall &&
                                                       !u_sckd.misoo_cpha1_rise));
  ERROR_cpha0_cpol1_toggle: assert property
  (@(posedge clk) disable iff (!rst_n)
   (!core_sckd_spcr.cpha &&  core_sckd_spcr.cpol) |-> (u_sckd.xfer0_fall && !core_sckd_spdr7_fall && !u_sckd.misoo_cpha0_fall &&
                                                       !u_sckd.misoo_cpha1_fall &&
                                                       !u_sckd.misoo_cpha1_rise));

  ERROR_cpha1_cpol0_toggle: assert property
  (@(posedge clk) disable iff (!rst_n)
   (core_sckd_spcr.cpha && !core_sckd_spcr.cpol) |-> (u_sckd.xfer0_rise && !core_sckd_spdr7_rise && !u_sckd.misoo_cpha0_rise &&
                                                      u_sckd.xfer0_fall && !core_sckd_spdr7_fall && !u_sckd.misoo_cpha0_fall &&
                                                      !u_sckd.misoo_cpha1_fall));

  ERROR_cpha1_cpol1_toggle: assert property
  (@(posedge clk) disable iff (!rst_n)
   (core_sckd_spcr.cpha &&  core_sckd_spcr.cpol) |-> (u_sckd.xfer0_rise && !core_sckd_spdr7_rise && !u_sckd.misoo_cpha0_rise &&
                                                      u_sckd.xfer0_fall && !core_sckd_spdr7_fall && !u_sckd.misoo_cpha0_fall &&
                                                      !u_sckd.misoo_cpha1_rise));

  ERROR_misoo_subtterm_onehot: assert property
  (@(posedge clk) disable iff (!rst_n)
   $onehot0({u_sckd.cpha0_lcell_out, u_sckd.misoo_cpha1_fall,  u_sckd.misoo_cpha1_rise}));

`endif //  `ifndef VERILATOR
   
endmodule: avr_spi
// Local Variables:
// verilog-auto-newline: nil
// verilog-auto-endcomments: t
// verilog-library-flags:("-y .")
// verilog-auto-ignore-concat:t
// verilog-typedef-regexp: "_t$"
// End:
