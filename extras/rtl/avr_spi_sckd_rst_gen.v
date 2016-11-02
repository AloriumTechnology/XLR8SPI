//////////////////////////////////////////////////////////////////
//=================================================================
//  Copyright(c) Superion Technology Group Inc., 2015
//  ALL RIGHTS RESERVED
//  $Id:  $
//=================================================================
//
// File name:  : avr_spi_sckd_rst_gen.v
// Author      : Greg Lund
// Description : sck domain logic for slave mosi and slave miso.
//
//=================================================================
///////////////////////////////////////////////////////////////////

`include "avr_spi_pkg.svh"

module avr_spi_sckd_rst_gen
  (input logic clk_scki,            // slave sck in
   input logic  ss_b, // slave's reset
   input logic  rst_n, // core reset
   
   // configuration (semi static)
   input        avr_spi_pkg::spcr_t core_sckd_spcr, // config (static)
   
   output logic rst_sckd_n
  );

  
  always_comb begin
    rst_sckd_n = !ss_b && rst_n && core_sckd_spcr.spe && !core_sckd_spcr.mstr;
  end
  

endmodule: avr_spi_sckd_rst_gen
// Local Variables:
// verilog-auto-newline: nil
// verilog-auto-endcomments: t
// verilog-library-flags:("-y .")
// verilog-auto-ignore-concat:t
// verilog-typedef-regexp: "_t$"
// End:

