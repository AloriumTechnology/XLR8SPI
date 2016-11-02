// *****************************************************************************************
//
// Version 0.1
// Modified 03.01.2007
// Designed by Ruslan Lepetenok
// *****************************************************************************************


// package bit_def_pack is

// Bit definitions for use with the IAR Assembler
// The Register Bit names are represented by their bit number (0-7).



// SPI Status Register
localparam    SPIF_bit  = 7;
localparam    WCOL_bit  = 6;
localparam    SPI2X_bit = 0;

// SPI Control Register
localparam    SPIE_bit = 7;
localparam    SPE_bit  = 6;
localparam    DORD_bit = 5;
localparam    MSTR_bit = 4;
localparam    CPOL_bit = 3;
localparam    CPHA_bit = 2;
localparam    SPR1_bit = 1;
localparam    SPR0_bit = 0;




localparam FCFGEN_BIT          = 0;
localparam FCFGTGT_BIT         = 1;
localparam FCFGCMP_BIT         = 3;  // write data complete. only valid on 32b granularity
localparam FCFGRDY_BIT         = 4;
localparam FCFGFM_BIT          = 5;
localparam FCFGOK_BIT          = 6;
localparam FCFGDN_BIT          = 7;
// end bit_def_pack;
