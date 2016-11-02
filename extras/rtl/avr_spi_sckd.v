//////////////////////////////////////////////////////////////////
//=================================================================
//  Copyright(c) Superion Technology Group Inc., 2015
//  ALL RIGHTS RESERVED
//  $Id:  $
//=================================================================
//
// File name:  : avr_spi_sckd.v
// Author      : Greg Lund
// Description : sck domain logic for slave mosi and slave miso.
//
//=================================================================
///////////////////////////////////////////////////////////////////

`include "avr_spi_pkg.svh"

module avr_spi_sckd
  (input logic clk_scki,            // slave sck in
   input logic        ss_b, // slave's reset
   input logic        rst_sckd_n,

   // configuration (semi static)
   input              avr_spi_pkg::spcr_t core_sckd_spcr, // config (static)

   // incoming path
   input logic        mosii, // slave mosi input
   output logic [1:0] sckd_core_mosi_cpt, // 0 = fall, 1 = rise
   output logic [1:0] sckd_core_scki_div2, // toggle on {rise,fall}

   // outgoing slave path
   input logic [7:0]  core_sckd_spdr_sh, // shift data register:for slave misoo using [6] or [7] based on mode & xfer
   input logic        core_sckd_spdr7_rise, // shift data register 7: cpha=0
   input logic        core_sckd_spdr7_fall, // shift data register 7: cpha=0

   output logic       misoo

   );


  logic               mosi_cpt_fall;
  logic               mosi_cpt_rise;
  logic               scki_div2_fall;
  logic               scki_div2_rise;


  //////////////////////////////////////////////////////////////////
    // posedge
  //////////////////////////////////////////////////////////////////
  always_ff @(posedge clk_scki)
    mosi_cpt_rise <= mosii;

  always_ff @(posedge clk_scki or negedge rst_sckd_n)
    if (!rst_sckd_n) begin
      scki_div2_rise <= '0;
    end
    else begin
      scki_div2_rise <= ~scki_div2_rise && core_sckd_spcr.spe && !core_sckd_spcr.mstr;
    end


  //////////////////////////////////////////////////////////////////
    // negedge
  //////////////////////////////////////////////////////////////////
  always_ff @(negedge clk_scki)
    mosi_cpt_fall <= mosii;

  always_ff @(negedge clk_scki or negedge rst_sckd_n)
    if (!rst_sckd_n) begin
      scki_div2_fall <= '0;
    end
    else begin
      scki_div2_fall <= ~scki_div2_fall && core_sckd_spcr.spe && !core_sckd_spcr.mstr;
    end

  //////////////////////////////////////////////////////////////////
  // to spi core
  //////////////////////////////////////////////////////////////////
  logic [2:0] xfer_cnt;         // posedge counts
  logic       xfer_cnt_zero;    // cnt == 0
  logic       xfer0_rise;
  logic       xfer0_fall;

  always_comb begin
    sckd_core_mosi_cpt = {mosi_cpt_rise, mosi_cpt_fall}; // 0 = fall, 1 = rise
    sckd_core_scki_div2 = {scki_div2_rise, scki_div2_fall}; // toggle on {rise,fall}
  end

  //////////////////////////////////////////////////////////////////
  // slave register, cpha==0
  //////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////
  // state
  logic misoo_cpha0_rise;             // sending xfer for registered path
  logic misoo_cpha0_fall;             // sending xfer for registered path
  logic rst_cpha0_rise_n;
  logic rst_cpha0_fall_n;
  always_comb begin
    rst_cpha0_rise_n = rst_sckd_n && !core_sckd_spcr.cpha && (core_sckd_spcr.cpha ^ core_sckd_spcr.cpol);
    rst_cpha0_fall_n = rst_sckd_n && !core_sckd_spcr.cpha && (core_sckd_spcr.cpha ^ ~core_sckd_spcr.cpol);
//    rst = !( rst_sckd_n && !core_sckd_spcr.cpha && (core_sckd_spcr.cpha ^ ~core_sckd_spcr.cpol))
//        =   !rst_sckd_n || core_sckd_spcr.cpha || (core_sckd_spcr.cpha != core_sckd_spcr.cpol)
//        =   !rst_sckd_n || core_sckd_spcr.cpha || core_sckd_spcr.cpol
  end

  always_ff @(posedge clk_scki or negedge rst_sckd_n)
    if (!rst_sckd_n) begin
      xfer_cnt <= '0;
      xfer_cnt_zero <= 1'b1;
    end
    else begin
      xfer_cnt <= xfer_cnt + 3'd1; // let this wrap
      xfer_cnt_zero <= &xfer_cnt;  //
    end

  always_ff @(posedge clk_scki or negedge rst_cpha0_rise_n)
    if (!rst_cpha0_rise_n) begin
      xfer0_rise <= 1'b1;
    end
    else begin
      xfer0_rise <= &xfer_cnt;
    end

  always_ff @(negedge clk_scki or negedge rst_cpha0_fall_n)
    if (!rst_cpha0_fall_n) begin
      xfer0_fall <= 1'b1;
    end
    else begin
      xfer0_fall <= xfer_cnt_zero;
    end

  always_ff @(posedge clk_scki or negedge rst_cpha0_rise_n)
    if (!rst_cpha0_rise_n) begin
      /*AUTORESET*/
      // Beginning of autoreset for uninitialized flops
      misoo_cpha0_rise <= 1'h0;
      // End of automatics
    end
    else begin
      misoo_cpha0_rise <= core_sckd_spdr_sh[6];
    end

  always_ff @(negedge clk_scki or negedge rst_cpha0_fall_n  )
    if (!rst_cpha0_fall_n) begin
      /*AUTORESET*/
      // Beginning of autoreset for uninitialized flops
      misoo_cpha0_fall <= 1'h0;
      // End of automatics
    end
    else begin
      misoo_cpha0_fall <=  core_sckd_spdr_sh[6];
    end

  // stage0: toggling parts of !cpha
  logic [1:0] cpha0_din;       // rise,fall part of !cpha
  logic [1:0] cpha0_lcell_out;
  always_comb begin
    cpha0_din[0] = xfer0_rise ? core_sckd_spdr7_rise : misoo_cpha0_rise;
    cpha0_din[1] = xfer0_fall ? core_sckd_spdr7_fall : misoo_cpha0_fall;
  end
  lcell cpha0_lcell_inst0(.in(cpha0_din[0]), .out(cpha0_lcell_out[0]));
  lcell cpha0_lcell_inst1(.in(cpha0_din[1]), .out(cpha0_lcell_out[1]));

  //////////////////////////////////////////////////////////////////
  // cpha==1 path
  //////////////////////////////////////////////////////////////////
  logic misoo_cpha1_rise;             // sending xfer for registered path
  logic misoo_cpha1_fall;             // sending xfer for registered path

  // following have resets to avoid Xs for dont care xfers.  Could remove if needed.
  logic rst_cpha1_rise_n;
  logic rst_cpha1_fall_n;
  always_comb begin
    rst_cpha1_rise_n = rst_sckd_n && core_sckd_spcr.cpha && (core_sckd_spcr.cpha ^ core_sckd_spcr.cpol);
    rst_cpha1_fall_n = rst_sckd_n && core_sckd_spcr.cpha && (core_sckd_spcr.cpha ^ ~core_sckd_spcr.cpol);
  end
  always_ff @(posedge clk_scki or negedge rst_cpha1_rise_n)
    if (!rst_cpha1_rise_n) begin
      /*AUTORESET*/
      // Beginning of autoreset for uninitialized flops
      misoo_cpha1_rise <= 1'h0;
      // End of automatics
    end
    else begin
      misoo_cpha1_rise <= core_sckd_spdr_sh[7];
    end

  always_ff @(negedge clk_scki or negedge rst_cpha1_fall_n  )
    if (!rst_cpha1_fall_n) begin
      /*AUTORESET*/
      // Beginning of autoreset for uninitialized flops
      misoo_cpha1_fall <= 1'h0;
      // End of automatics
    end
    else begin
      misoo_cpha1_fall <=  core_sckd_spdr_sh[7];
    end // else: !if(!rst_cpha1_fall_n)

  //////////////////////////////////////////////////////////////////
  // now second stage
  // only one of [0..2] will toggle in a given mode.  cpha, !cpha&&cpol, !cpha&&!cpol
  //////////////////////////////////////////////////////////////////
  
  lcell misoo_lcell_inst(.in((|cpha0_lcell_out) ||  misoo_cpha1_fall || misoo_cpha1_rise), .out(misoo));
  
endmodule: avr_spi_sckd
// Local Variables:
// verilog-auto-newline: nil
// verilog-auto-endcomments: t
// verilog-library-flags:("-y .")
// verilog-auto-ignore-concat:t
// verilog-typedef-regexp: "_t$"
// End:

