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
//  1. NOTE: Fixed bit assignments for SPCR.  See spcr_t typdef in avr_spi_pkg
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

module avr_spi_core
  #(parameter DESIGN_CONFIG = 9,       // use default image
    parameter SPCR_Address    = 6'h2C, // SPI Control Register
    parameter SPSR_Address    = 6'h2D, // SPI Status Register
    parameter SPDR_Address    = 6'h2E // SPI I/O Data Registerparameter SPCR_Addr,
    )
  (// AVR Control
   input              rst_n,
   input              clk,
   input              clken,

   // CSR
   input [5:0]        adr,
   input [7:0]        dbus_in,
   output reg [7:0]   dbus_out,
   input              iore,
   input              iowe,
   output reg         out_en,

   // sckd
   input logic [1:0]  sckd_core_mosi_cpt, // 0 = fall, 1 = rise
   input logic [1:0]  sckd_core_scki_div2, // toggle on {rise,fall}
   output             avr_spi_pkg::spcr_t core_sckd_spcr, // config (static)
   output logic [7:0] core_sckd_spdr_sh, // shift data register:for slave misoo using [6] or [7] based on mode & xfer
   output logic       core_sckd_spdr7_rise, // shift data register 7: cpha=0
   output logic       core_sckd_spdr7_fall, // shift data register 7: cpha=0

   //
   // SPI i/f
   input              misoi,
   input              mosii,
   input              scki, // Resynch
   input              ss_b, // Resynch
   output reg         misoo,
   output reg         mosio,
   output reg         scko,
   output             spe,
   output             spimaster,

   // SRAM space
   input wire [7:0]   ramadr,
   input wire         ramre,
   input wire         ramwe,
   input wire         dm_sel,

   // IRQ
   output             spiirq,
   input              spiack,
   // Slave Programming Mode
   input              por,
   input              spiextload,
   output             spidwrite,
   output             spiload
   );

  // Resynch
  logic              ss_b_resync;
  logic              rst_ss_n;  // reset from SS input


  avr_spi_pkg::spcr_t spcr;
  avr_spi_pkg::spcr_t spcr_nxt;
  //   wire [7:0]          SPSR;

  //reg [7:0]          SPSR;
  //   `define SPIF SPSR[7]
  //   `define WCOL SPSR[6]
  //   `define SPI2X SPSR[0]

  reg               SPIF_Current;
  reg               wcol_current;
  reg               SPI2X_Current;


  reg               SPI2X_Next;

  reg [7:0]         SPDR_Rc;
  reg [7:0]         SPDR_Rc_Next;
  reg [7:0]         SPDR_Sh_Current;
  reg [7:0]         SPDR_Sh_Next;

  reg [5:0]         Div_Next;
  reg [5:0]         Div_Current;
  reg               Div_Toggle;

  reg               DivCntMsb_Current;
  reg               DivCntMsb_Next;

  typedef enum      logic [3:0]
                    { MSTR_IDLE = 4'd0,
                      MSTR_B0 = 4'd1,
                      MSTR_B1 = 4'd2,
                      MSTR_B2 = 4'd3,
                      MSTR_B3 = 4'd4,
                      MSTR_B4 = 4'd5,
                      MSTR_B5 = 4'd6,
                      MSTR_B6 = 4'd7,
                      MSTR_B7 = 4'd8} mstr_st_t;
  mstr_st_t           mstr_ps; // master mode present state
  mstr_st_t          mstr_ns;

  wire              tr_start;

  reg               scko_Next;
  reg               scko_Current;               //!!!

  reg               UpdRcDataRg_Current;
  reg               UpdRcDataRg_Next;

  reg               TmpIn_Current;
  reg               TmpIn_Next;

  // Slave
  typedef enum logic [3:0] {SLAVE_IDLE = 4'd0,
                            SLAVE_B0I = 4'd1,
                            SLAVE_B0 = 4'd2,
                            SLAVE_B1 = 4'd3,
                            SLAVE_B2 = 4'd4,
                            SLAVE_B3 = 4'd5,
                            SLAVE_B4 = 4'd6,
                            SLAVE_B5 = 4'd7,
                            SLAVE_B6 = 4'd8,
                            SLAVE_B6W = 4'd9} slave_st_t;
  slave_st_t slave_ps;
  slave_st_t slave_ns;

   // SIF clear SM
  reg          SPIFClrSt_Current;
  reg          SPIFClrSt_Next;

  // WCOL clear SM
   reg                 WCOLClrSt_Current;
   reg                 WCOLClrSt_Next;

   reg                 SPIF_Next;
   reg                 wcol_nxt;

   reg                 MstDSamp_Next;
   reg                 MstDSamp_Current;


   function[7:0] Fn_RevBitVector;
      input [7:0]        InVector;
   begin
      Fn_RevBitVector = {InVector[0],InVector[1],InVector[2],InVector[3],InVector[4],InVector[5],InVector[6],InVector[7]};
   end
   endfunction

  //////////////////////////////////////////////////////////////////
  // CSR decoding.  Following other blocks defintions like xlr8_counter16.v
  //////////////////////////////////////////////////////////////////
  localparam  SPCR_DM_LOC    = (SPCR_Address >= 16'h60) ? 1 : 0;
  logic spcr_sel;
  logic spcr_we;
  logic spcr_re;
  always_comb begin
    spcr_sel = SPCR_DM_LOC ? (dm_sel && (ramadr == SPCR_Address)) : (adr == SPCR_Address);
    spcr_we = spcr_sel && (SPCR_DM_LOC ?  ramwe : iowe);
    spcr_re = spcr_sel && (SPCR_DM_LOC ?  ramre : iore);
  end

  localparam  SPSR_DM_LOC    = (SPSR_Address >= 16'h60) ? 1 : 0;
  logic spsr_sel;
  logic spsr_we;
  logic spsr_re;
  always_comb begin
    spsr_sel = SPSR_DM_LOC ? (dm_sel && (ramadr == SPSR_Address)) : (adr == SPSR_Address);
    spsr_we = spsr_sel && (SPSR_DM_LOC ?  ramwe : iowe);
    spsr_re = spsr_sel && (SPSR_DM_LOC ?  ramre : iore);
  end

  localparam  SPDR_DM_LOC    = (SPDR_Address >= 16'h60) ? 1 : 0;
  logic spdr_sel;
  logic spdr_we;
  logic spdr_re;
  always_comb begin
    spdr_sel = SPDR_DM_LOC ? (dm_sel && (ramadr == SPDR_Address)) : (adr == SPDR_Address);
    spdr_we = spdr_sel && (SPDR_DM_LOC ?  ramwe : iowe);
    spdr_re = spdr_sel && (SPDR_DM_LOC ?  ramre : iore);
  end


  //////////////////////////////////////////////////////////////////
  // slave input path
  //////////////////////////////////////////////////////////////////

  // reset


  rsnc_bit #(.add_stgs_num(0), .inv_f_stgs(0))
  u_ss_b_rsnc(
              .clk(clk),
              .din(ss_b),
              .dout(ss_b_resync)
              );

  // need to register to guarantee no glitches
  always_ff @(posedge clk)  begin
    rst_ss_n <= !(ss_b_resync && spcr.spe && !spcr.mstr) && rst_n;
  end

  //////////////////////////////////////////////////////////////////
  // resync sampling
  logic scki_div2_mux;           // select capture control
  logic scki_div2_sync;

  always_comb begin
    scki_div2_mux = sckd_core_scki_div2[~spcr.cpol ^ spcr.cpha];
  end
  /* rsnc_bit AUTO_TEMPLATE (
   .din(scki_div2_mux),
   .dout(scki_div2_sync),
   );*/

  rsnc_bit  #(.add_stgs_num(0), .inv_f_stgs(0))  u_sck_div2_sync
    (/*AUTOINST*/
     // Outputs
     .dout                              (scki_div2_sync),        // Templated
     // Inputs
     .clk                               (clk),
     .din                               (scki_div2_mux));         // Templated

  //////////////////////////////////////////////////////////////////
  // capture edge
  logic scki_div2_sync_d;
  always_ff @(posedge clk)
    scki_div2_sync_d <= scki_div2_sync;

  logic slv_smp_adv;                // advance slave sampling (input)
  logic slv_din;
  always_comb slv_smp_adv = scki_div2_sync_d ^ scki_div2_sync;
  always_comb slv_din     = sckd_core_mosi_cpt[~spcr.cpol ^ spcr.cpha];

  //////////////////////////////////////////////////////////////////
  // resync driving
  logic scki_drv_div2_mux;
  logic scki_drv_div2_sync;
  logic scki_drv_div2_sync_d;
  logic slv_drv_adv;
  always_comb begin
    scki_drv_div2_mux = sckd_core_scki_div2[spcr.cpol ^ spcr.cpha];
  end

  /* rsnc_bit AUTO_TEMPLATE (
   .din(scki_drv_div2_mux),
   .dout(scki_drv_div2_sync),
   );*/

  rsnc_bit  #(.add_stgs_num(0), .inv_f_stgs(0))  u_sck_drv_div2_sync
    (/*AUTOINST*/
     // Outputs
     .dout                              (scki_drv_div2_sync),    // Templated
     // Inputs
     .clk                               (clk),
     .din                               (scki_drv_div2_mux));     // Templated

  //////////////////////////////////////////////////////////////////
  // capture edge
  always_ff @(posedge clk)
    scki_drv_div2_sync_d <= scki_drv_div2_sync;

  always_comb slv_drv_adv = scki_drv_div2_sync_d ^ scki_drv_div2_sync;

  //////////////////////////////////////////////////////////////////
  // drive sckd
  always_comb begin
    core_sckd_spcr = spcr;
    core_sckd_spdr_sh = SPDR_Sh_Current;
  end


  always @(negedge rst_n or posedge clk) begin
    if (!rst_n)  begin

      spcr <= {8{1'b0}};

    SPIF_Current <= 1'b0;
    wcol_current <= 1'b0;
    SPI2X_Current <= 1'b0;

    Div_Current <= {6{1'b0}};
    DivCntMsb_Current <= 1'b0;

    mstr_ps <= MSTR_IDLE;
    //         slave_ps <= SLAVE_IDLE;

    SPDR_Sh_Current <= {8{1'b1}};
    SPDR_Rc <= {8{1'b0}};

    SPIFClrSt_Current <= 1'b0;
    WCOLClrSt_Current <= 1'b0;

    scko <= 1'b0;
    scko_Current <= 1'b0;
    misoo <= 1'b0;
    mosio <= 1'b0;

    TmpIn_Current <= 1'b0;
    UpdRcDataRg_Current <= 1'b0;
    MstDSamp_Current <= 1'b0;
    /*AUTORESET*/
    // Beginning of autoreset for uninitialized flops
    core_sckd_spdr7_fall <= 1'h0;
    core_sckd_spdr7_rise <= 1'h0;
    // End of automatics
  end

    else  if (clken) begin

      spcr <= spcr_nxt;

      SPIF_Current <= SPIF_Next;
      SPI2X_Current <= SPI2X_Next;
      wcol_current <= wcol_nxt;

      Div_Current <= Div_Next;
      DivCntMsb_Current <= DivCntMsb_Next;
      mstr_ps <= (spcr.spe && spcr.mstr) ? mstr_ns :
                 MSTR_IDLE;

      //         slave_ps <= slave_ns;
      SPDR_Sh_Current <= SPDR_Sh_Next;
      core_sckd_spdr7_rise <= !(spcr.spe && !spcr.mstr) ? 1'b0 : 
                              tr_start ? (SPDR_Sh_Next[7] && !spcr.cpha && spcr.cpol) :
                               core_sckd_spdr7_rise;
      core_sckd_spdr7_fall <= !(spcr.spe && !spcr.mstr) ? 1'b0 : 
                              tr_start ? (SPDR_Sh_Next[7] && !spcr.cpha && !spcr.cpol) :
                               core_sckd_spdr7_fall;

      SPDR_Rc <= SPDR_Rc_Next;
      SPIFClrSt_Current <= SPIFClrSt_Next;
      WCOLClrSt_Current <= WCOLClrSt_Next;

      scko_Current <= scko_Next;
      scko <= scko_Next;
      misoo <= SPDR_Sh_Next[7];
      mosio <= SPDR_Sh_Next[7];

      TmpIn_Current <= TmpIn_Next;
      UpdRcDataRg_Current <= UpdRcDataRg_Next;
      MstDSamp_Current <= MstDSamp_Next;
    end

  end // SeqPrc

  always_ff @(posedge clk or negedge rst_ss_n)
    if (!rst_ss_n) begin
      slave_ps <= SLAVE_IDLE;
    end
    else begin
      slave_ps <= (spcr.spe && !spcr.mstr) ? slave_ns :
                  SLAVE_IDLE;
    end

  always_comb begin
    spcr_nxt = spcr_we ? dbus_in : spcr;
    SPI2X_Next = spsr_we ? dbus_in[0] : SPI2X_Current;
  end

 //  rle
 //  assign SPSR[5:1] = {5{1'b0}};

   // Divider
   // SPI2X | SPR1 | SPR0 | SCK Frequency
   //   0   |  0   |   0  | fosc /4       (2)
   //   0   |  0   |   1  | fosc /16       (8)
   //   0   |  1   |   0  | fosc /64       (32)
   //   0   |  1   |   1  | fosc /128      (64)
   // ------+------+------+-------------
   //   1   |  0   |   0  | fosc /2        (1)
   //   1   |  0   |   1  | fosc /8        (4)
   //   1   |  1   |   0  | fosc /32       (16)
   //   1   |  1   |   1  | fosc /64       (32)


   always_comb begin
      Div_Toggle = 1'b0;
      if (mstr_ps != MSTR_IDLE)
      begin
         if (SPI2X_Current == 1'b1)             // Extended mode
            case (spcr.spr)
               2'b00 :          // fosc /2
                     Div_Toggle = 1'b1;
               2'b01 :          // fosc /8
                  if (Div_Current == 6'b000011)
                     Div_Toggle = 1'b1;
               2'b10 :          // fosc /32
                  if (Div_Current == 6'b001111)
                     Div_Toggle = 1'b1;
               2'b11 :          // fosc /64
                  if (Div_Current == 6'b011111)
                     Div_Toggle = 1'b1;
               default :
                  Div_Toggle = 1'b0;
            endcase
         else
            // Normal mode
            case (spcr.spr)
               2'b00 :          // fosc /4
                  if (Div_Current == 6'b000001)
                     Div_Toggle = 1'b1;
               2'b01 :          // fosc /16
                  if (Div_Current == 6'b000111)
                     Div_Toggle = 1'b1;
               2'b10 :          // fosc /64
                  if (Div_Current == 6'b011111)
                     Div_Toggle = 1'b1;
               2'b11 :          // fosc /128
                  if (Div_Current == 6'b111111)
                     Div_Toggle = 1'b1;
               default :
                  Div_Toggle = 1'b0;
            endcase
      end
   end


   always_comb begin
      Div_Next = Div_Current;
      DivCntMsb_Next = DivCntMsb_Current;
      if (mstr_ps != MSTR_IDLE)
      begin
         if (Div_Toggle == 1'b1)
         begin
            Div_Next = {6{1'b0}};
            DivCntMsb_Next = (~DivCntMsb_Current);
         end
         else
            Div_Next = Div_Current + 6'd1;
      end

   end

   assign tr_start = ((spdr_we & spcr.spe == 1'b1)) ? 1'b1 : 1'b0;

   // Transmitter Master Mode Shift Control SM

   always_comb begin
      mstr_ns = mstr_ps;
      case (mstr_ps)
         MSTR_IDLE :
            if (tr_start == 1'b1 & spcr.mstr)
               mstr_ns = MSTR_B0;
         MSTR_B0 :
            if (DivCntMsb_Current == 1'b1 & Div_Toggle == 1'b1)
               mstr_ns = MSTR_B1;
         MSTR_B1 :
            if (DivCntMsb_Current == 1'b1 & Div_Toggle == 1'b1)
               mstr_ns = MSTR_B2;
         MSTR_B2 :
            if (DivCntMsb_Current == 1'b1 & Div_Toggle == 1'b1)
               mstr_ns = MSTR_B3;
         MSTR_B3 :
            if (DivCntMsb_Current == 1'b1 & Div_Toggle == 1'b1)
               mstr_ns = MSTR_B4;
         MSTR_B4 :
            if (DivCntMsb_Current == 1'b1 & Div_Toggle == 1'b1)
               mstr_ns = MSTR_B5;
         MSTR_B5 :
            if (DivCntMsb_Current == 1'b1 & Div_Toggle == 1'b1)
               mstr_ns = MSTR_B6;
         MSTR_B6 :
            if (DivCntMsb_Current == 1'b1 & Div_Toggle == 1'b1)
               mstr_ns = MSTR_B7;
         MSTR_B7 :
            if (DivCntMsb_Current == 1'b1 & Div_Toggle == 1'b1)
               mstr_ns = MSTR_IDLE;
         default :
            mstr_ns = MSTR_IDLE;
      endcase
   end


   always_comb begin
      SPIFClrSt_Next = SPIFClrSt_Current;
      case (SPIFClrSt_Current)
         1'b0 :
            if (spsr_re & (SPIF_Current == 1'b1) & spcr.spe)
               SPIFClrSt_Next = 1'b1;
         1'b1 :
            if (spdr_re || spdr_we)
               SPIFClrSt_Next = 1'b0;
         default :
            SPIFClrSt_Next = SPIFClrSt_Current;
      endcase
   end  //SPIFClrCombProc


  always_comb begin
    WCOLClrSt_Next = WCOLClrSt_Current;
    case (WCOLClrSt_Current)
      1'b0 :
        if (spsr_re && wcol_current)
          WCOLClrSt_Next = 1'b1;
      1'b1 :
        if (spdr_re || spdr_we)
          WCOLClrSt_Next = 1'b0;
      default :
        WCOLClrSt_Next = WCOLClrSt_Current;
    endcase
  end //WCOLClrCombProc


  always_comb begin
    MstDSamp_Next = 1'b0;
    case (MstDSamp_Current)
      1'b0 :
        if (mstr_ps != MSTR_IDLE)
          begin
            if (spcr.cpha == spcr.cpol)
              begin
                if (scko_Next == 1'b1 & scko_Current == 1'b0)           // Rising edge
                  MstDSamp_Next = 1'b1;
              end
            else
              // CPHA/=CPOL
              if (scko_Next == 1'b0 & scko_Current == 1'b1)             // Falling edge
                MstDSamp_Next = 1'b1;
          end
      1'b1 :
        MstDSamp_Next = 1'b0;
      default :
        MstDSamp_Next = 1'b0;
    endcase
  end // MstDataSamplingComb

  //

  always_comb begin
      UpdRcDataRg_Next = 1'b0;
      case (UpdRcDataRg_Current)
        1'b0 :
          if ((spcr.mstr & mstr_ps != MSTR_IDLE & mstr_ns == MSTR_IDLE) | (!spcr.mstr & slave_ps != SLAVE_IDLE & slave_ns == SLAVE_IDLE))
            UpdRcDataRg_Next = 1'b1;
        1'b1 :
          UpdRcDataRg_Next = 1'b0;
        default :
          UpdRcDataRg_Next = 1'b0;
      endcase
  end

  always_comb begin
    TmpIn_Next = TmpIn_Current;
    if (spcr.mstr & MstDSamp_Next == 1'b1)              // Master mode
      TmpIn_Next = misoi;

    // FIXME: care about this if ss_b ?
    else if (!spcr.mstr & slv_smp_adv & ss_b_resync == 1'b0)            // Slave mode ???
      TmpIn_Next = slv_din;
  end

  always_comb begin // ShiftRgComb
    SPDR_Sh_Next = SPDR_Sh_Current;
    if (tr_start && (mstr_ps == MSTR_IDLE) && (slave_ps == SLAVE_IDLE) && !(!spcr.mstr && slv_smp_adv && !ss_b_resync)) begin   // Load
      if (spcr.dord == 1'b1)            // the LSB of the data word is transmitted first
        SPDR_Sh_Next = Fn_RevBitVector(dbus_in);
      else
        // the MSB of the data word is transmitted first
        SPDR_Sh_Next = dbus_in;
    end
    else if (spcr.mstr && UpdRcDataRg_Current) begin
      // GEL: this make MOSI go to a 1 after a xfer
      SPDR_Sh_Next[7] = 1'b1;
    end
    else if ((spcr.mstr &&  (mstr_ps != MSTR_IDLE) && DivCntMsb_Current && Div_Toggle) ||
             (!spcr.mstr && /* (slave_ps != SLAVE_IDLE) && */ slv_drv_adv && !ss_b_resync))
      // Shift
      SPDR_Sh_Next = {SPDR_Sh_Current[7 - 1:0], TmpIn_Current};
  end //ShiftRgComb


  always_comb begin // sckoGenComb
    scko_Next = scko_Current;
    if (spcr_we)                // Write to spcr
      scko_Next = dbus_in[3];           // CPOL
    else if (tr_start  && spcr.cpha &&( mstr_ps == MSTR_IDLE))
      scko_Next = (~spcr.cpol);
    else if (mstr_ps != MSTR_IDLE & mstr_ns == MSTR_IDLE)               // "Parking"
      scko_Next = spcr.cpol;
    else if (mstr_ps != MSTR_IDLE & DivCntMsb_Current != DivCntMsb_Next)
      scko_Next = (~scko_Current);
  end // always_comb

               // Receiver data register

  always_comb begin // : SPDRRcComb
    SPDR_Rc_Next = SPDR_Rc;
    if (UpdRcDataRg_Current == 1'b1) begin
        if (!spcr.mstr & spcr.cpha == 1'b1) begin
          if (spcr.dord == 1'b1)                // the LSB of the data word is transmitted first
            SPDR_Rc_Next = Fn_RevBitVector({SPDR_Sh_Current[7 - 1:0], TmpIn_Current});
          else
              // the MSB of the data word is transmitted first
            SPDR_Rc_Next = {SPDR_Sh_Current[7 - 1:0], TmpIn_Current};
        end
        else
          if (spcr.dord == 1'b1)                // the LSB of the data word is transmitted first
            SPDR_Rc_Next = Fn_RevBitVector(SPDR_Sh_Current);
          else
            // the MSB of the data word is transmitted first
            SPDR_Rc_Next = SPDR_Sh_Current;
    end // if (UpdRcDataRg_Current == 1'b1)
  end // always_comb


  //****************************************************************************************
  // Slave
  //****************************************************************************************

  // Slave Master Mode Shift Control SM

  always_comb begin
    slave_ns = slave_ps;
    if (ss_b_resync == 1'b0)
      case (slave_ps)
        SLAVE_IDLE :

          if (!spcr.mstr)
            begin
              if (spcr.cpha)
                begin
                  if (slv_drv_adv)
                    slave_ns = SLAVE_B0;
                end
              else
                //      CPHA='0'
                if (slv_smp_adv)
                  slave_ns = SLAVE_B0I;
            end

        SLAVE_B0I :
          if (slv_drv_adv)
            slave_ns = SLAVE_B0;

        SLAVE_B0 :
          if (slv_drv_adv)
            slave_ns = SLAVE_B1;
        SLAVE_B1 :
          if (slv_drv_adv)
            slave_ns = SLAVE_B2;
        SLAVE_B2 :
          if (slv_drv_adv)
            slave_ns = SLAVE_B3;
        SLAVE_B3 :
          if (slv_drv_adv)
            slave_ns = SLAVE_B4;
        SLAVE_B4 :
          if (slv_drv_adv)
            slave_ns = SLAVE_B5;
        SLAVE_B5 :
          if (slv_drv_adv)
            slave_ns = SLAVE_B6;

        SLAVE_B6 :
          if (slv_drv_adv)
            begin
              if (spcr.cpha == 1'b0)
                slave_ns = SLAVE_IDLE;
              else
                // CPHA='1'
                slave_ns = SLAVE_B6W;
            end

        SLAVE_B6W :
          if (slv_smp_adv)
            slave_ns = SLAVE_IDLE;
        default :
          slave_ns = SLAVE_IDLE;
      endcase
  end // block: SlvSMNextComb

  //////////////////////////////////////////////////////////////////
  // calculate collision status
  //////////////////////////////////////////////////////////////////
  localparam [3:0][4:0] SCK_PW_TIME = {5'd16,5'd8, 5'd4, 5'd2};
  localparam [4:0] SCK_PW = SCK_PW_TIME[DESIGN_CONFIG[2:1]];
  
  localparam RESYNC_TIME = 3;
  localparam TRSTART_W = $clog2(SCK_PW + RESYNC_TIME + 1);
  logic [TRSTART_W-1:0] trstart_cnt_dwn;
  
  
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) begin
      trstart_cnt_dwn <= '0;
    end
    else begin
      trstart_cnt_dwn <= tr_start ? (spcr.cpha ? 5'd4 :
                                     (SCK_PW + 5'd4)) :
                         |trstart_cnt_dwn ? trstart_cnt_dwn - 5'd1 :
                         '0;
    end // else: !if(!rst_n)
  
  
  always_comb begin: calc_wcol
    logic set_wcol;
    logic clr_wcol;

    set_wcol = (spdr_we && (spcr.mstr ? (mstr_ps != MSTR_IDLE) : (slave_ps != SLAVE_IDLE))) ||
               (spcr.spe && !spcr.mstr &&  (|trstart_cnt_dwn) && (spcr.cpha ? slv_drv_adv : slv_smp_adv));
    clr_wcol = (spdr_we || spdr_re) && WCOLClrSt_Current;

    wcol_nxt = set_wcol ||
               (wcol_current && !clr_wcol);

  end


  always_comb begin
    SPIF_Next = SPIF_Current;
    case (SPIF_Current)
      1'b0 :
        if ((!spcr.mstr & slave_ps != SLAVE_IDLE & slave_ns == SLAVE_IDLE) | (spcr.mstr & mstr_ps != MSTR_IDLE & mstr_ns == MSTR_IDLE))
          SPIF_Next = 1'b1;
      1'b1 :
        if (((spdr_re || spdr_we)  & SPIFClrSt_Current == 1'b1) | spiack == 1'b1)
          SPIF_Next = 1'b0;
      default :
        SPIF_Next = SPIF_Current;
    endcase
  end

  //*************************************************************************************

  assign spimaster = spcr.mstr;
  assign spe = spcr.spe;

  // IRQ
  assign spiirq = spcr.spie & SPIF_Current;


  always_comb begin
    dbus_out = (spcr_re ? spcr : 8'd0) |
               (spsr_re ? {SPIF_Current, wcol_current, {5{1'b0}},SPI2X_Current}: 8'd0) |
               (spdr_re ? SPDR_Rc  : 8'd0);
    out_en =   spcr_re |
               spsr_re |
               spdr_re;
  end // always_comb


  //
  assign spidwrite = 1'b0;
  assign spiload = 1'b0;

`ifdef STGI_ASSERT_ON

  //ERROR_write_collision: assert property
  //(@(posedge clk) disable iff (!rst_n)
  // !wcol_current);
  
  `ifndef VERILATOR
  ERROR_undefined_ss_b_resync: assert property
    (@(posedge clk) disable iff (!rst_n || !clken)
   spcr.spe |-> !$isunknown(ss_b_resync));


 `ifdef OVL_END_OF_SIMULATION
   ERROR_idle_slave_ps: assert property
   (@(posedge clk) disable iff (!rst_n)
    `OVL_END_OF_SIMULATION |-> (slave_ps == SLAVE_IDLE));
   ERROR_idle_mstr_ps: assert property
   (@(posedge clk) disable iff (!rst_n)
    `OVL_END_OF_SIMULATION |-> (mstr_ps == MSTR_IDLE));
 `endif

   ERROR_slave_ps_undefined: assert property
   (@(posedge clk) disable iff (!rst_n)
    !$isunknown(slave_ps));
   ERROR_mstr_ps_undefined: assert property
   (@(posedge clk) disable iff (!rst_n)
    !$isunknown(mstr_ps));
   
    
  `endif
 `endif //  `ifdef STGI_ASSERT_ON

endmodule: avr_spi_core
// Local Variables:
// verilog-auto-newline: nil
// verilog-auto-endcomments: t
// verilog-library-flags:("-y .")
// verilog-auto-ignore-concat:t
// verilog-typedef-regexp: "_t$"
// End:
