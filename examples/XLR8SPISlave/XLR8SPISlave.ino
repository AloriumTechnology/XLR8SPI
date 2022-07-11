//_______________________________________________________________________________ 
//
// XLR8SPISlave - super simple spi data transfer test.
//  Data is sent from master to slave. Then checked and reported on slave.
//  An XLR8SPI object is set up to use the default Arduino SPI interface.
//  SCK is pin 13
//  MISO is pin 12
//  MOSI is pin 11
//  SS is pin 10
//
//_______________________________________________________________________________ 


#include <XLR8SPI.h>

#define CHIPSEL 10

// Initialize a SPI object using Arduino's builtin SPI registers
XLR8SPIClass XLR8SPI(0x4c, 0x4d, 0x4e);

char buf [100];
volatile byte pos;
volatile boolean process_it;
static int passcnt = 24;
int cnt = 0;

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

String s;
void setup (void)
{

  XLR8SPI.setPins(13,12,11,CHIPSEL);
  Serial.begin (115200);   // debugging

  Serial.println("Hello Slave");

  // turn on SPI in slave mode
  XLR8SPI.writeSPCR(XLR8SPI.readSPCR() | bit (SPE));

  // have to send on master in, *slave out*
  pinMode(MISO, OUTPUT);
  
  // get ready for an interrupt
  pos = 0;   // buffer empty
  process_it = false;

  // now turn on interrupts
  XLR8SPI.attachInterrupt();

  while (1) {
    if (process_it) {
      buf [pos] = 0;  
      s = buf;
      // Serial.print("buf:\""); Serial.println (buf); Serial.println("\"");
      // Serial.print("s:\""); Serial.print(s); Serial.println("\"");
      // Serial.print("p[cnt]:\""); Serial.print(p[cnt]); Serial.println("\"");
      // Serial.print("cnt:"); Serial.println(cnt);
      pos = 0;
      process_it = false;

      if( s == p[0] || s == p[1] || s == p[2] || s == p[3]) { 
        Serial.println("Transfer OK.");      
        Serial.print("Received:"); Serial.println(s);     
        if (cnt == passcnt) {
           Serial.println("PASSED.");
           break;
        }  
      } else  {
        Serial.println("FAILED."); 
        Serial.print("Received:"); Serial.println(s);
        Serial.print("Expected:"); Serial.println(p[cnt]);
        break;
      }
      cnt++;
    }  // end if(process_it)
  } // end while
}  // end of setup


// SPI interrupt routine
ISR (SPI_STC_vect)
{
  byte c = XLR8SPI.readSPDR();  // grab byte from SPI Data Register
  
  // add to buffer if room
  if (pos < sizeof buf)
  {
    buf [pos++] = c;
    // example: newline means time to process buffer
    if (c == '\n')
      process_it = true;

  }  // end of room available
}  // end of interrupt routine SPI_STC_vect

// main loop - wait for flag set in interrupt routine
void loop (void)
{
  if (process_it)
  {
    buf [pos] = 0;  
    s = buf;
    // Serial.print("buf:\""); Serial.println (buf); Serial.println("\"");
    // Serial.print("s:\""); Serial.print(s); Serial.println("\"");
    // Serial.print("p[cnt]:\""); Serial.print(p[cnt]); Serial.println("\"");
    // Serial.print("cnt:"); Serial.println(cnt);
    pos = 0;
    process_it = false;

    if( s == p[0] || s == p[1] || s == p[2] || s == p[3] ||
        s == p[4] || s == p[5] || s == p[6] || s == p[7] ||
        s == p[8] || s == p[9] || s == p[10] || s == p[11] ||
        s == p[12] || s == p[13] || s == p[14] || s == p[15] ||
        s == p[16] || s == p[17] || s == p[18] || s == p[19] || 
        s == p[20] || s == p[21] || s == p[22] || s == p[23] 
      ) {
      Serial.println("Transfer OK.");
      Serial.print("Received:"); Serial.println(s);
      if (cnt == passcnt) {
         Serial.println("PASSED.");
         while(1) {};
      }
    } else  {
      Serial.println("FAILED."); 
      Serial.print("Received:"); Serial.println(s);
      Serial.print("Expected:"); Serial.println(p[cnt]);
      while(1) {};
    }
    cnt++;
  }  // end of flag set

}  // end of loop

