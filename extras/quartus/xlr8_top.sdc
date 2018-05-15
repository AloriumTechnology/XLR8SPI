#**********************************************************************
# SDC constraints for XLR8SPI
#**********************************************************************

# Create Clock 
create_clock -name clk_xlr8_spi_scki -period $base_clk_period  [get_pins {xb_openxlr8_inst|clk_xlr8_spi_scki_buffer|combout}]


# Set Clock Uncertainty
set_clock_uncertainty -to [get_clocks {clk_xlr8_spi_scki}] 0.5

