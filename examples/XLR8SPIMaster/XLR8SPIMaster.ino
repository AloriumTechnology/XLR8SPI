//_______________________________________________________________________________
//
// XLR8SPIMaster - super simple spi data transfer test.
//  Data is sent from master to slave. Then checked and reported on slave.
//  An XLR8SPI object is set up to use the default Arduino SPI interface.
//  SCK is pin 13
//  MISO is pin 12
//  MOSI is pin 11
//  SS is pin 10
//
//_______________________________________________________________________________

#include <XLR8SPI.h>

#define XB_SPCR_Address 0xAC
#define XB_SPSR_Address 0xAD
#define XB_SPDR_Address 0xAE

#define RSTPIN  9

#define CHIPSEL 4

// Initialize a SPI object using Arduino's builtin SPI registers
XLR8SPIClass XLR8SPI(XB_SPCR_Address, XB_SPSR_Address, XB_SPDR_Address);

int cnt = 24;

String p[] = {"a5a5a5a5a5a5a5a5\n", 
              "3c3c3c3c3c3c3c3c\n",
              "f0e0d0c0b0a09181716151423210\n", 
              "deaddeaddeaddead\n", 
              "0000000000000008\n", 
              "8000000000000000\n", 
              "0000000000000080\n", 
              "0800000000000000\n", 
              "0000000000000800\n", 
              "0080000000000000\n", 
              "0000000000008000\n", 
              "0008000000000000\n", 
              "0000000000080000\n", 
              "0000800000000000\n", 
              "0000000000800000\n", 
              "0000080000000000\n", 
              "0000000008000000\n", 
              "0000008000000000\n", 
              "0000000080000000\n", 
              "0000000800000000\n", 
              "Now is the time for all good men to come to the aid of their party\n", 
              "7478489845904380\n",
              "It was a dark and lonely night!!\n", 
              "800010000010000010000000200000200000002000002000002000004000004000004\n"};

char buffer[30];

void setup (void)
{
  char c;

  XLR8SPI.setPins(7,6,5,CHIPSEL);
  Serial.begin(115200);
  Serial.print("Start\n");
  for (int i=0;  i<p[0].length() ; i++)
    Serial.print(p[0].charAt(i));
  Serial.print("End\n");
  
  pinMode(RSTPIN, OUTPUT);   //Device NRST
  pinMode(CHIPSEL, OUTPUT);
  
 
  // reset the part
  // ---------------------------------------------------------------------
  digitalWrite(RSTPIN, LOW);   // Assert reset
  delay(1);
  digitalWrite(RSTPIN, HIGH);  // Release reset

  digitalWrite(CHIPSEL, HIGH);  // ensure SS stays high for now

  Serial.print("Pre-Begin");
  Serial.println();
  Serial.print("SPCR: ");
  Serial.print(XLR8SPI.readSPCR());
  Serial.print("  SPSR: ");
  Serial.print(XLR8SPI.readSPSR());
  Serial.print("  SPDR: ");
  Serial.print(XLR8SPI.readSPDR());
  Serial.println();
  Serial.println();

  // Put SCK, MOSI, SS pins into output mode
  // also put SCK, MOSI into LOW state, and SS into HIGH state.
  // Then put SPI hardware into Master mode and turn SPI on
  XLR8SPI.begin ();

  Serial.print("Post-Begin");
  Serial.println();
  Serial.print("SPCR: ");
  Serial.print(XLR8SPI.readSPCR());
  Serial.print("  SPSR: ");
  Serial.print(XLR8SPI.readSPSR());
  Serial.print("  SPDR: ");
  Serial.print(XLR8SPI.readSPDR());
  Serial.println();
  Serial.println();

  // Slow down the master a bit
  XLR8SPI.setClockDivider(XLR8_SPI_CLOCK_DIV8);

  Serial.print("Set Clock Divide");
  Serial.println();
  Serial.print("SPCR: ");
  Serial.print(XLR8SPI.readSPCR());
  Serial.print("  SPSR: ");
  Serial.print(XLR8SPI.readSPSR());
  Serial.print("  SPDR: ");
  Serial.print(XLR8SPI.readSPDR());
  Serial.println();
  Serial.println();

}  // end of setup


void loop (void)
{

  char c;

  // enable Slave Select
  digitalWrite(CHIPSEL, LOW);    

  // send test string
  for (int i=0; i<cnt; i++) {

    // enable Slave Select
    digitalWrite(CHIPSEL, LOW);    
  
    for (int j=0;  j < p[i].length() ; j++) {

       // Serial.print("i:"); Serial.print(i); Serial.print(" j:"); Serial.println(j);

      // enable Slave Select
      digitalWrite(CHIPSEL, LOW);    

      c = p[i].charAt(j);
      Serial.print(c);
      XLR8SPI.transfer (c);
 
      Serial.print("Transfer");
      Serial.println();
      Serial.print("SPCR: ");
      Serial.print(XLR8SPI.readSPCR());
      Serial.print("  SPSR: ");
      Serial.print(XLR8SPI.readSPSR());
      Serial.print("  SPDR: ");
      Serial.print(XLR8SPI.readSPDR());
      Serial.println();
      Serial.println();
    }

    // disable Slave Select
    digitalWrite(CHIPSEL, HIGH);

    delay (100);  // 1 seconds delay 
  
  }
}  // end of loop

