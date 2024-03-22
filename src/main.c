/**
 * \proj Lab4
 * \brief Program to interface with an IR receiver & displayed received messages on OLED screen
 * \author Corbin Warmbier, Akhil Sharma
 *
 */

// Standard includes
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <math.h>

// Driverlib includes
#include "hw_types.h"
#include "gpio.h"
#include "hw_gpio.h"
#include "hw_memmap.h"
#include "hw_common_reg.h"
#include "hw_ints.h"
#include "debug.h"
#include "spi.h"
#include "systick.h"
#include "rom.h"
#include "rom_map.h"
#include "utils.h"
#include "prcm.h"
#include "uart.h"
#include "interrupt.h"
#include "timer.h"
#include "glcdfont.h"
#include "test.h"

// Common interface includes
#include "uart_if.h"
#include "pinmux.h"
#include "timer_if.h"
#include "gpio_if.h"
#include "common.h"
#include "Adafruit_SSD1351.h"
#include "Adafruit_GFX.h"

// Simplelink includes
#include "simplelink.h"

// LAB 4
#define MAX_URI_SIZE 128
#define URI_SIZE MAX_URI_SIZE + 1


#define APPLICATION_NAME        "SSL"
#define APPLICATION_VERSION     "1.1.1.EEC.Winter2024"
#define SERVER_NAME             "a2j6hmwcg5gfcl-ats.iot.us-east-1.amazonaws.com"
#define GOOGLE_DST_PORT         8443

#define SL_SSL_CA_CERT "/cert/rootCA.der" //starfield class2 rootca (from firefox) // <-- this one works
#define SL_SSL_PRIVATE "/cert/private.der"
#define SL_SSL_CLIENT  "/cert/client.der"


//NEED TO UPDATE THIS FOR IT TO WORK!
#define DATE                13     /* Current Date */
#define MONTH               3     /* Month 1-12 */
#define YEAR                2024  /* Current year */
#define HOUR                15    /* Time - hours */
#define MINUTE              50    /* Time - minutes */
#define SECOND              0     /* Time - seconds */

#define POSTHEADER "POST /things/CC3200_Board/shadow HTTP/1.1\r\n"
#define GETHEADER "GET /things/CC3200_Board/shadow HTTP/1.1\r\n"
#define HOSTHEADER "Host: a2j6hmwcg5gfcl-ats.iot.us-east-1.amazonaws.com\r\n"
#define CHEADER "Connection: Keep-Alive\r\n"
#define CTHEADER "Content-Type: application/json; charset=utf-8\r\n"
#define CLHEADER1 "Content-Length: "
#define CLHEADER2 "\r\n\r\n"


#define SPI_IF_BIT_RATE  100000
#define TR_BUFF_SIZE     100

#define UART_PRINT       Report
#define NVIC_ST_CURRENT  0xE000E018


#define BLACK           0x0000
#define BLUE            0x001F
#define GREEN           0x07E0
#define CYAN            0x07FF
#define RED             0xF800
#define MAGENTA         0xF81F
#define YELLOW          0xFFE0
#define WHITE           0xFFFF


//*****************************************************************************
//                 GLOBAL VARIABLES -- Start
//*****************************************************************************
volatile unsigned char IR_intflag = 0;
volatile unsigned char SysTick_Reset = 1;
volatile int data_index = 0;

static volatile unsigned long g_ulSysTickValue;
static volatile unsigned long g_ulBase;
static volatile unsigned long g_ulTimerExpired = 0;
static volatile unsigned long g_ulIntClearVector;
static volatile int done_rec = 0;

#if defined(ccs)
extern void (* const g_pfnVectors[])(void);
#endif
#if defined(ewarm)
extern uVectorEntry __vector_table;
#endif

// some helpful macros for systick

// the cc3200's fixed clock frequency of 80 MHz
// note the use of ULL to indicate an unsigned long long constant
#define SYSCLKFREQ 80000000ULL

// macro to convert ticks to microseconds
#define TICKS_TO_US(ticks) \
    ((((ticks) / SYSCLKFREQ) * 1000000ULL) + \
    ((((ticks) % SYSCLKFREQ) * 1000000ULL) / SYSCLKFREQ))\

// macro to convert microseconds to ticks
#define US_TO_TICKS(us) ((SYSCLKFREQ / 1000000ULL) * (us))

// systick reload value set to 40ms period
// (PERIOD_SEC) * (SYSCLKFREQ) = PERIOD_TICKS
#define SYSTICK_RELOAD_VAL 3200000UL

volatile int index = 0;
volatile int start_cmd = 0;
volatile int packets_rec = 0;
static int packet1[8];
static int packet2[8];
static int packet3[8];
static int packet4[8];
static char DATA1[2048];
static char DATA_B[1024];
volatile char letter;
volatile long lRetVal = -1;

extern void (* const g_pfnVectors[])(void);

static double distances[10];

volatile int UART_Flag = 0;
volatile int Btn_held = 0;
// Direction Decoding
// 0 for Neutral
// 1 for Left
// 2 for Right
volatile int direction = 0;
volatile int prev_direction;

int currentX_sen = 60;
int currentY_sen = 40;
int currentX_char = 0;
int currentY_char = 0;

int charWidth = 5;    // Width of each character in bytes
int charHeight = 7;   // Height of each character in pixels
int spacing = 1;      // Space between characters
int first_run_printOLED = 1;

extern void (* const g_pfnVectors[])(void);

static double median;
static double prevMedian;
static char buffer[20];
static char prevBuffer[20];

typedef struct PinSetting {
    unsigned long port;
    unsigned int pin;
} PinSetting;

static PinSetting IR_in = { .port = GPIOA0_BASE, .pin = 0x80};

///** LAB 4 **/
// Application specific status/error codes
typedef enum{
    // Choosing -0x7D0 to avoid overlap w/ host-driver's error codes
    LAN_CONNECTION_FAILED = -0x7D0,
    INTERNET_CONNECTION_FAILED = LAN_CONNECTION_FAILED - 1,
    DEVICE_NOT_IN_STATION_MODE = INTERNET_CONNECTION_FAILED - 1,

    STATUS_CODE_MAX = -0xBB8
}e_AppStatusCodes;

typedef struct
{
   /* time */
   unsigned long tm_sec;
   unsigned long tm_min;
   unsigned long tm_hour;
   /* date */
   unsigned long tm_day;
   unsigned long tm_mon;
   unsigned long tm_year;
   unsigned long tm_week_day; //not required
   unsigned long tm_year_day; //not required
   unsigned long reserved[3];
}SlDateTime;

volatile unsigned long  g_ulStatus = 0;//SimpleLink Status
unsigned long  g_ulPingPacketsRecv = 0; //Number of Ping Packets received
unsigned long  g_ulGatewayIP = 0; //Network Gateway IP address
unsigned char  g_ucConnectionSSID[SSID_LEN_MAX+1]; //Connection SSID
unsigned char  g_ucConnectionBSSID[BSSID_LEN_MAX]; //Connection BSSID
signed char    *g_Host = SERVER_NAME;
SlDateTime g_time;

//*****************************************************************************
//                 GLOBAL VARIABLES -- End
//*****************************************************************************


//****************************************************************************
//                      LOCAL FUNCTION PROTOTYPES
//****************************************************************************
static long WlanConnect();
static int set_time();
static void BoardInit(void);
static long InitializeAppVariables();
static int tls_connect();
static int connectToAccessPoint();
static int http_post(int);
////static int http_get(int);

//*****************************************************************************
//                 USER FUNCTIONS -- Start
//*****************************************************************************

void printCharacter(char character) {
    int asciiValue = (int)character;
    int totalCharWidth = charWidth + spacing;
    int fontIndex = asciiValue * charWidth; // Calculate the starting index of the character in the font array
    int col;
    int bit;

    // Logic for newline character
    if(character == '\n') {
        currentX_char = 0;
        currentY_char += charHeight;
        return;
    }


    // Check if we need to wrap to the next line
    if (currentX_char + totalCharWidth > width()) {
        currentX_char = 0; // Reset X to the beginning of the line
        currentY_char += charHeight; // Move Y to the next line
    }

    // Draw Character
    for (col = 0; col < charWidth; col++) {
        for (bit = 0; bit < charHeight; bit++) {
            drawPixel(currentX_char + col, currentY_char + bit, BLACK);
        }
    }

    // Draw Column
    for (col = 0; col < charWidth; col++) {
        for (bit = 0; bit < charHeight; bit++) {
            if (font[fontIndex + col] & (1 << bit)) {
                drawPixel(currentX_char + col, currentY_char + bit, WHITE);
            }
        }
    }
    currentX_char += charWidth;
}

void printHeader(void) {
    currentX_char = 0;
    currentY_char = 0;
    char header_msg[1024];
    sprintf(header_msg, "=====[ SwivelFind ]=====\n\nRev. Mar 12\n\0");
    int i = 0;
    for(i = 0; header_msg[i] != '\0'; i++) {
        printCharacter(header_msg[i]);
    }
}

void printFloatToOLED(float number) {
    char distance_header[64];
    // Buffer to store the string representation of the float
    snprintf(buffer, sizeof(buffer), "%.2f", number); // Convert float to string with 2 decimal places

    int length = strlen(buffer);
    int totalCharWidth = charWidth + spacing;

    // Save the previous current value

    snprintf(prevBuffer, sizeof(prevBuffer), "%.2f", prevMedian); // Assuming currentValue is the previously displayed value

    // Clear the screen to black
//    fillScreen(BLACK);
//    printHeader();
    fillRect(0, 40, 128, 20, BLACK);
    UART_PRINT("Prev distance: %f mm\n\r", prevMedian);


    int i = 0;
    int col, bit;
    currentX_char = 0;
    currentY_char = 40;
    sprintf(distance_header, "Current: \0");
    for(i = 0; distance_header[i] != '\0'; i++) {
        printCharacter(distance_header[i]);
    }

    // Print the new value at the top
    for (i = 0; i < length; i++) {
        char character = buffer[i];
        int asciiValue = (int)character;
        int fontIndex = asciiValue * charWidth;

        // Draw each column of the character
        for (col = 0; col < charWidth; col++) {
            for (bit = 0; bit < charHeight; bit++) {
                if (font[fontIndex + col] & (1 << bit)) {
                    drawPixel(currentX_sen + col + (i * totalCharWidth), currentY_sen + bit, WHITE);
                } else {
                    drawPixel(currentX_sen + col + (i * totalCharWidth), currentY_sen + bit, BLACK);
                }
            }
        }
    }

    currentX_char = 0;
    currentY_char = 50;
    sprintf(distance_header, "Previous: \0");
    for(i = 0; distance_header[i] != '\0'; i++) {
        printCharacter(distance_header[i]);
    }
    for (i = 0; i < strlen(prevBuffer); i++) {
        char character = prevBuffer[i];
        int asciiValue = (int)character;
        int fontIndex = asciiValue * charWidth;

        // Draw each column of the character
        for (col = 0; col < charWidth; col++) {
            for (bit = 0; bit < charHeight; bit++) {
                if (font[fontIndex + col] & (1 << bit)) {
                    drawPixel(currentX_sen + col + (i * totalCharWidth), currentY_sen + 10 + bit, WHITE);
                } else {
                    drawPixel(currentX_sen + col + (i * totalCharWidth), currentY_sen + 10 + bit, BLACK);
                }
            }
        }
    }
}

void sortArray(int n) {
    int i, j;
    double key;
    for (i = 1; i < n; i++) {
        key = distances[i];
        j = i - 1;

        while (j >= 0 && distances[j] > key) {
            distances[j + 1] = distances[j];
            j = j - 1;
        }
        distances[j + 1] = key;
    }
}

static void findDistance(void) {
    int i;
    for (i = 0; i < 10; i++) {
        // Set Trig High
        GPIOPinWrite(GPIOA1_BASE, 0x10, 0x10);

        delay(10);

        // Set Trig Low
        GPIOPinWrite(GPIOA1_BASE, 0x10, 0x0);

        while(!GPIOPinRead(GPIOA2_BASE, 0x2));

        Timer_IF_Start(g_ulBase, TIMER_A, 10000);

        while(GPIOPinRead(GPIOA2_BASE, 0x2));
        distances[i] = ((800000 -  (0xFFFFFFFF - Timer_IF_GetCount(g_ulBase, TIMER_A)) / 1000) * 0.21);
    }
    sortArray(10);

//    if (10 % 2 == 0) {
//       // Even number of readings
//       median = (distances[10/2 - 1] + distances[10/2]) / 2.0;
//    } else {
//       // Odd number of readings
//       median = distances[5];
//    }
    median = distances[4];

       // Print the median distance
    //float bearing = readBearingHMC5883L();
    UART_PRINT("Median distance: %f mm\n\r", median);
}

static void bufferPrint() {
    int i;
    if (g_ulTimerExpired == 2) {
        g_ulTimerExpired = 0;
    }
    int addr_ret = 0;
    int addr_i = 0;
    for (i = 7; i > -1; i--) {
        addr_ret += packet1[i]*(pow(2, addr_i));
        addr_i++;
    }
    int data_ret = 0;
    int data_i = 0;
    for (i = 7; i > -1; i--) {
        data_ret += packet3[i]*(pow(2, data_i));
        data_i++;
    }
    switch (data_ret) {
        case 136:
            UART_PRINT("Button 1 Pressed\n\r");
            buffer[6] = '\0';
            sprintf(DATA1, "{\"state\": {\r\n\"desired\" : {\r\n\"Current\" : \"%s\"\r\n}}}\r\n\r\n", buffer);
            http_post(lRetVal);
            break;
        case 72:
            UART_PRINT("Button 2 Pressed\n\r");
            prevBuffer[6] = '\0';
            sprintf(DATA1, "{\"state\": {\r\n\"desired\" : {\r\n\"Previous\" : \"%s\"\r\n}}}\r\n\r\n", prevBuffer);
            http_post(lRetVal);
            break;
        case 200:
            UART_PRINT("Button 3 Pressed\n\r");
            buffer[6] = '\0';
            prevBuffer[6] = '\0';
            sprintf(DATA1, "{\"state\": {\r\n\"desired\" : {\r\n\"Current\" : \"%s\", \r\n\"Previous\" : \"%s\"\r\n}}}\r\n\r\n", buffer, prevBuffer);
            http_post(lRetVal);
            break;
        case 40:
            UART_PRINT("Button 4 Pressed\n\r");
            direction = 1;
            prev_direction = 1;
            break;
        case 168:
            UART_PRINT("Button 5 Pressed\n\r");
            direction = 0;
            prev_direction = 0;
            Message("===[Finding Distance]===\n\r");
            prevMedian = median;
            findDistance();
            printFloatToOLED(median);
            //printToOLED(median);
            break;
        case 104:
            UART_PRINT("Button 6 Pressed\n\r");
            direction = 2;
            prev_direction = 2;
            break;
        default:
            UART_PRINT("Unknown Button Received\n\r");
            direction = 0;
            prev_direction = 0;
            break;
    }
    g_ulTimerExpired = 2;
}

static void turnMotor(int direction) {
    // Set Enable to High
    if (direction == 0) {
        return;
    }
    GPIOPinWrite(GPIOA1_BASE, 0x40, 0x0);
    // Set Direction Pin to High (Right)
    if(direction == 2) {
        GPIOPinWrite(GPIOA0_BASE, 0x10, 0x10);
    } else {
        GPIOPinWrite(GPIOA0_BASE, 0x10, 0x0);
    }
    GPIOPinWrite(GPIOA0_BASE, 0x40, 0x40);
    delay(2);
    GPIOPinWrite(GPIOA0_BASE, 0x40, 0x0);
    delay(2);
}



//*****************************************************************************
//                 USER FUNCTIONS -- End
//*****************************************************************************


//*****************************************************************************
//                 HANDLER FUNCTIONS -- Start
//*****************************************************************************

/**
 * Timer Handler for IR Remote Timeout
 */
void TimerBaseIntHandler(void) {
    //
    // Clear the timer interrupt.
    //
    Timer_IF_InterruptClear(g_ulBase);
}

/**
 * Reset SysTick Counter
 */
static inline void SysTickReset(void) {
    // any write to the ST_CURRENT register clears it
    // after clearing it automatically gets reset without
    // triggering exception logic
    // see reference manual section 3.2.1
    HWREG(NVIC_ST_CURRENT) = 1;
}

/**
 * SysTick Interrupt Handler
 *
 * Keep track of whether the systick counter wrapped
 */
static void SysTickHandler(void) {
    SysTick_Reset = 1;
}

/**
 * GPIO Interrupt Handler for BaseA0
 */
static void GPIOA0IntHandler(void) { // IR_in handler
    unsigned long ulStatus;

    ulStatus = MAP_GPIOIntStatus(GPIOA0_BASE, true);
    if (packets_rec == 0) {
        MAP_GPIOIntClear(GPIOA0_BASE, ulStatus);        // clear interrupts on GPIOA0
        IR_intflag=1;
    }
    if (SysTick_Reset == 0) {
        // read the countdown register and compute elapsed cycles
        uint64_t delta_us = TICKS_TO_US(SYSTICK_RELOAD_VAL - SysTickValueGet());
        SysTickReset();
        // 0 detected
        if (index == 32) {
            bufferPrint();
            index = 0;
            start_cmd = 0;
            UART_PRINT("Button Was Pressed In Direction: %d\n\r", direction);
            turnMotor(direction);
        }
        if (start_cmd == 1 && 800 < delta_us && delta_us < 1750) {
            if (index < 8) {
                packet1[index] = 0;
            } else if (index < 16) {
                packet2[index - 8] = 0;
            } else if (index < 24) {
                packet3[index - 16] = 0;
            } else {
                packet4[index - 24] = 0;
            }
            index++;
        }
        // 1 detected
        else if (start_cmd == 1 && 2000 < delta_us && delta_us < 2500) {
            if (index < 8) {
                packet1[index] = 1;
            } else if (index < 16) {
                packet2[index - 8] = 1;
            }  else if (index < 24) {
                packet3[index - 16] = 1;
            } else {
                packet4[index - 24] = 1;
            }
            index++;
        }
        // Leader Code Interrupt Detected
        else if(12000 < delta_us && delta_us < 14500) {
            index = 0;
            start_cmd = 1;
        } else if(10000 < delta_us && delta_us < 12000){
            UART_PRINT("Button Was Held In Direction: %d\n\r", prev_direction);
            turnMotor(prev_direction);
            index = 0;
            start_cmd = 1;
        }
    } else {
        direction = 0;
        SysTick_Reset = 0;  // Clear SysTick reset flag
        SysTickReset();
    }
}

//*****************************************************************************
//                 HANDLER FUNCTIONS -- End
//*****************************************************************************


//*****************************************************************************
//                 INIT FUNCTIONS -- Start
//*****************************************************************************

/**
 * Initializes SysTick Module
 */
static void SysTickInit(void) {

    // configure the reset value for the systick countdown register
    MAP_SysTickPeriodSet(SYSTICK_RELOAD_VAL);

    // register interrupts on the systick module
    MAP_SysTickIntRegister(SysTickHandler);

    // enable interrupts on systick
    // (trigger SysTickHandler when countdown reaches 0)
    MAP_SysTickIntEnable();

    // enable the systick module itself
    MAP_SysTickEnable();
}









// ----------------------------------------------------------------------------



/* ================================= [LAB 4 Functions] ==================================*/
//*****************************************************************************
// SimpleLink Asynchronous Event Handlers -- Start
//*****************************************************************************


//*****************************************************************************
//
//! \brief The Function Handles WLAN Events
//!
//! \param[in]  pWlanEvent - Pointer to WLAN Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkWlanEventHandler(SlWlanEvent_t *pWlanEvent) {
    if(!pWlanEvent) {
        return;
    }

    switch(pWlanEvent->Event) {
        case SL_WLAN_CONNECT_EVENT: {
            SET_STATUS_BIT(g_ulStatus, STATUS_BIT_CONNECTION);

            //
            // Information about the connected AP (like name, MAC etc) will be
            // available in 'slWlanConnectAsyncResponse_t'.
            // Applications can use it if required
            //
            //  slWlanConnectAsyncResponse_t *pEventData = NULL;
            // pEventData = &pWlanEvent->EventData.STAandP2PModeWlanConnected;
            //

            // Copy new connection SSID and BSSID to global parameters
            memcpy(g_ucConnectionSSID,pWlanEvent->EventData.
                   STAandP2PModeWlanConnected.ssid_name,
                   pWlanEvent->EventData.STAandP2PModeWlanConnected.ssid_len);
            memcpy(g_ucConnectionBSSID,
                   pWlanEvent->EventData.STAandP2PModeWlanConnected.bssid,
                   SL_BSSID_LENGTH);

            UART_PRINT("[WLAN EVENT] STA Connected to the AP: %s , "
                       "BSSID: %x:%x:%x:%x:%x:%x\n\r",
                       g_ucConnectionSSID,g_ucConnectionBSSID[0],
                       g_ucConnectionBSSID[1],g_ucConnectionBSSID[2],
                       g_ucConnectionBSSID[3],g_ucConnectionBSSID[4],
                       g_ucConnectionBSSID[5]);
        }
        break;

        case SL_WLAN_DISCONNECT_EVENT: {
            slWlanConnectAsyncResponse_t*  pEventData = NULL;

            CLR_STATUS_BIT(g_ulStatus, STATUS_BIT_CONNECTION);
            CLR_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_AQUIRED);

            pEventData = &pWlanEvent->EventData.STAandP2PModeDisconnected;

            // If the user has initiated 'Disconnect' request,
            //'reason_code' is SL_USER_INITIATED_DISCONNECTION
            if(SL_USER_INITIATED_DISCONNECTION == pEventData->reason_code) {
                UART_PRINT("[WLAN EVENT]Device disconnected from the AP: %s,"
                    "BSSID: %x:%x:%x:%x:%x:%x on application's request \n\r",
                           g_ucConnectionSSID,g_ucConnectionBSSID[0],
                           g_ucConnectionBSSID[1],g_ucConnectionBSSID[2],
                           g_ucConnectionBSSID[3],g_ucConnectionBSSID[4],
                           g_ucConnectionBSSID[5]);
            }
            else {
                UART_PRINT("[WLAN ERROR]Device disconnected from the AP AP: %s, "
                           "BSSID: %x:%x:%x:%x:%x:%x on an ERROR..!! \n\r",
                           g_ucConnectionSSID,g_ucConnectionBSSID[0],
                           g_ucConnectionBSSID[1],g_ucConnectionBSSID[2],
                           g_ucConnectionBSSID[3],g_ucConnectionBSSID[4],
                           g_ucConnectionBSSID[5]);
            }
            memset(g_ucConnectionSSID,0,sizeof(g_ucConnectionSSID));
            memset(g_ucConnectionBSSID,0,sizeof(g_ucConnectionBSSID));
        }
        break;

        default: {
            UART_PRINT("[WLAN EVENT] Unexpected event [0x%x]\n\r",
                       pWlanEvent->Event);
        }
        break;
    }
}

//*****************************************************************************
//
//! \brief This function handles network events such as IP acquisition, IP
//!           leased, IP released etc.
//!
//! \param[in]  pNetAppEvent - Pointer to NetApp Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkNetAppEventHandler(SlNetAppEvent_t *pNetAppEvent) {
    if(!pNetAppEvent) {
        return;
    }

    switch(pNetAppEvent->Event) {
        case SL_NETAPP_IPV4_IPACQUIRED_EVENT: {
            SlIpV4AcquiredAsync_t *pEventData = NULL;

            SET_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_AQUIRED);

            //Ip Acquired Event Data
            pEventData = &pNetAppEvent->EventData.ipAcquiredV4;

            //Gateway IP address
            g_ulGatewayIP = pEventData->gateway;

            UART_PRINT("[NETAPP EVENT] IP Acquired: IP=%d.%d.%d.%d , "
                       "Gateway=%d.%d.%d.%d\n\r",
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,3),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,2),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,1),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.ip,0),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,3),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,2),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,1),
            SL_IPV4_BYTE(pNetAppEvent->EventData.ipAcquiredV4.gateway,0));
        }
        break;

        default: {
            UART_PRINT("[NETAPP EVENT] Unexpected event [0x%x] \n\r",
                       pNetAppEvent->Event);
        }
        break;
    }
}


//*****************************************************************************
//
//! \brief This function handles HTTP server events
//!
//! \param[in]  pServerEvent - Contains the relevant event information
//! \param[in]    pServerResponse - Should be filled by the user with the
//!                                      relevant response information
//!
//! \return None
//!
//****************************************************************************
void SimpleLinkHttpServerCallback(SlHttpServerEvent_t *pHttpEvent, SlHttpServerResponse_t *pHttpResponse) {
    // Unused in this application
}

//*****************************************************************************
//
//! \brief This function handles General Events
//!
//! \param[in]     pDevEvent - Pointer to General Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkGeneralEventHandler(SlDeviceEvent_t *pDevEvent) {
    if(!pDevEvent) {
        return;
    }

    //
    // Most of the general errors are not FATAL are are to be handled
    // appropriately by the application
    //
    UART_PRINT("[GENERAL EVENT] - ID=[%d] Sender=[%d]\n\n",
               pDevEvent->EventData.deviceEvent.status,
               pDevEvent->EventData.deviceEvent.sender);
}


//*****************************************************************************
//
//! This function handles socket events indication
//!
//! \param[in]      pSock - Pointer to Socket Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkSockEventHandler(SlSockEvent_t *pSock) {
    if(!pSock) {
        return;
    }

    switch( pSock->Event ) {
        case SL_SOCKET_TX_FAILED_EVENT:
            switch( pSock->socketAsyncEvent.SockTxFailData.status) {
                case SL_ECLOSE:
                    UART_PRINT("[SOCK ERROR] - close socket (%d) operation "
                                "failed to transmit all queued packets\n\n",
                                    pSock->socketAsyncEvent.SockTxFailData.sd);
                    break;
                default:
                    UART_PRINT("[SOCK ERROR] - TX FAILED  :  socket %d , reason "
                                "(%d) \n\n",
                                pSock->socketAsyncEvent.SockTxFailData.sd, pSock->socketAsyncEvent.SockTxFailData.status);
                  break;
            }
            break;

        default:
            UART_PRINT("[SOCK EVENT] - Unexpected Event [%x0x]\n\n",pSock->Event);
          break;
    }
}


//*****************************************************************************
// SimpleLink Asynchronous Event Handlers -- End breadcrumb: s18_df
//*****************************************************************************


//*****************************************************************************
//
//! \brief This function initializes the application variables
//!
//! \param    0 on success else error code
//!
//! \return None
//!
//*****************************************************************************
static long InitializeAppVariables() {
    g_ulStatus = 0;
    g_ulGatewayIP = 0;
    g_Host = SERVER_NAME;
    memset(g_ucConnectionSSID,0,sizeof(g_ucConnectionSSID));
    memset(g_ucConnectionBSSID,0,sizeof(g_ucConnectionBSSID));
    return SUCCESS;
}


//*****************************************************************************
//! \brief This function puts the device in its default state. It:
//!           - Set the mode to STATION
//!           - Configures connection policy to Auto and AutoSmartConfig
//!           - Deletes all the stored profiles
//!           - Enables DHCP
//!           - Disables Scan policy
//!           - Sets Tx power to maximum
//!           - Sets power policy to normal
//!           - Unregister mDNS services
//!           - Remove all filters
//!
//! \param   none
//! \return  On success, zero is returned. On error, negative is returned
//*****************************************************************************
static long ConfigureSimpleLinkToDefaultState() {
    SlVersionFull   ver = {0};
    _WlanRxFilterOperationCommandBuff_t  RxFilterIdMask = {0};

    unsigned char ucVal = 1;
    unsigned char ucConfigOpt = 0;
    unsigned char ucConfigLen = 0;
    unsigned char ucPower = 0;

    long lRetVal = -1;
    long lMode = -1;

    lMode = sl_Start(0, 0, 0);
    ASSERT_ON_ERROR(lMode);

    // If the device is not in station-mode, try configuring it in station-mode
    if (ROLE_STA != lMode) {
        if (ROLE_AP == lMode) {
            // If the device is in AP mode, we need to wait for this event
            // before doing anything
            while(!IS_IP_ACQUIRED(g_ulStatus)) {
#ifndef SL_PLATFORM_MULTI_THREADED
              _SlNonOsMainLoopTask();
#endif
            }
        }

        // Switch to STA role and restart
        lRetVal = sl_WlanSetMode(ROLE_STA);
        ASSERT_ON_ERROR(lRetVal);

        lRetVal = sl_Stop(0xFF);
        ASSERT_ON_ERROR(lRetVal);

        lRetVal = sl_Start(0, 0, 0);
        ASSERT_ON_ERROR(lRetVal);

        // Check if the device is in station again
        if (ROLE_STA != lRetVal) {
            // We don't want to proceed if the device is not coming up in STA-mode
            return DEVICE_NOT_IN_STATION_MODE;
        }
    }

    // Get the device's version-information
    ucConfigOpt = SL_DEVICE_GENERAL_VERSION;
    ucConfigLen = sizeof(ver);
    lRetVal = sl_DevGet(SL_DEVICE_GENERAL_CONFIGURATION, &ucConfigOpt,
                                &ucConfigLen, (unsigned char *)(&ver));
    ASSERT_ON_ERROR(lRetVal);

    UART_PRINT("Host Driver Version: %s\n\r",SL_DRIVER_VERSION);
    UART_PRINT("Build Version %d.%d.%d.%d.31.%d.%d.%d.%d.%d.%d.%d.%d\n\r",
    ver.NwpVersion[0],ver.NwpVersion[1],ver.NwpVersion[2],ver.NwpVersion[3],
    ver.ChipFwAndPhyVersion.FwVersion[0],ver.ChipFwAndPhyVersion.FwVersion[1],
    ver.ChipFwAndPhyVersion.FwVersion[2],ver.ChipFwAndPhyVersion.FwVersion[3],
    ver.ChipFwAndPhyVersion.PhyVersion[0],ver.ChipFwAndPhyVersion.PhyVersion[1],
    ver.ChipFwAndPhyVersion.PhyVersion[2],ver.ChipFwAndPhyVersion.PhyVersion[3]);

    // Set connection policy to Auto + SmartConfig
    //      (Device's default connection policy)
    lRetVal = sl_WlanPolicySet(SL_POLICY_CONNECTION,
                                SL_CONNECTION_POLICY(1, 0, 0, 0, 1), NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Remove all profiles
    lRetVal = sl_WlanProfileDel(0xFF);
    ASSERT_ON_ERROR(lRetVal);



    //
    // Device in station-mode. Disconnect previous connection if any
    // The function returns 0 if 'Disconnected done', negative number if already
    // disconnected Wait for 'disconnection' event if 0 is returned, Ignore
    // other return-codes
    //
    lRetVal = sl_WlanDisconnect();
    if(0 == lRetVal) {
        // Wait
        while(IS_CONNECTED(g_ulStatus)) {
#ifndef SL_PLATFORM_MULTI_THREADED
              _SlNonOsMainLoopTask();
#endif
        }
    }

    // Enable DHCP client
    lRetVal = sl_NetCfgSet(SL_IPV4_STA_P2P_CL_DHCP_ENABLE,1,1,&ucVal);
    ASSERT_ON_ERROR(lRetVal);

    // Disable scan
    ucConfigOpt = SL_SCAN_POLICY(0);
    lRetVal = sl_WlanPolicySet(SL_POLICY_SCAN , ucConfigOpt, NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Set Tx power level for station mode
    // Number between 0-15, as dB offset from max power - 0 will set max power
    ucPower = 0;
    lRetVal = sl_WlanSet(SL_WLAN_CFG_GENERAL_PARAM_ID,
            WLAN_GENERAL_PARAM_OPT_STA_TX_POWER, 1, (unsigned char *)&ucPower);
    ASSERT_ON_ERROR(lRetVal);

    // Set PM policy to normal
    lRetVal = sl_WlanPolicySet(SL_POLICY_PM , SL_NORMAL_POLICY, NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Unregister mDNS services
    lRetVal = sl_NetAppMDNSUnRegisterService(0, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Remove  all 64 filters (8*8)
    memset(RxFilterIdMask.FilterIdMask, 0xFF, 8);
    lRetVal = sl_WlanRxFilterSet(SL_REMOVE_RX_FILTER, (_u8 *)&RxFilterIdMask,
                       sizeof(_WlanRxFilterOperationCommandBuff_t));
    ASSERT_ON_ERROR(lRetVal);

    lRetVal = sl_Stop(SL_STOP_TIMEOUT);
    ASSERT_ON_ERROR(lRetVal);

    InitializeAppVariables();

    return lRetVal; // Success
}




//****************************************************************************
//
//! \brief Connecting to a WLAN Accesspoint
//!
//!  This function connects to the required AP (SSID_NAME) with Security
//!  parameters specified in te form of macros at the top of this file
//!
//! \param  None
//!
//! \return  0 on success else error code
//!
//! \warning    If the WLAN connection fails or we don't aquire an IP
//!            address, It will be stuck in this function forever.
//
//****************************************************************************
static long WlanConnect() {
    SlSecParams_t secParams = {0};
    long lRetVal = 0;

    secParams.Key = SECURITY_KEY;
    secParams.KeyLen = strlen(SECURITY_KEY);
    secParams.Type = SECURITY_TYPE;

    UART_PRINT("Attempting connection to access point: ");
    UART_PRINT(SSID_NAME);
    UART_PRINT("... ...");
    lRetVal = sl_WlanConnect(SSID_NAME, strlen(SSID_NAME), 0, &secParams, 0);
    ASSERT_ON_ERROR(lRetVal);

    UART_PRINT(" Connected!!!\n\r");


    // Wait for WLAN Event
    while((!IS_CONNECTED(g_ulStatus)) || (!IS_IP_ACQUIRED(g_ulStatus))) {
        // Toggle LEDs to Indicate Connection Progress
        _SlNonOsMainLoopTask();
        GPIO_IF_LedOff(MCU_IP_ALLOC_IND);
        MAP_UtilsDelay(800000);
        _SlNonOsMainLoopTask();
        GPIO_IF_LedOn(MCU_IP_ALLOC_IND);
        MAP_UtilsDelay(800000);
    }

    return SUCCESS;

}




long printErrConvenience(char * msg, long retVal) {
    UART_PRINT(msg);
    GPIO_IF_LedOn(MCU_RED_LED_GPIO);
    return retVal;
}


//*****************************************************************************
//
//! This function updates the date and time of CC3200.
//!
//! \param None
//!
//! \return
//!     0 for success, negative otherwise
//!
//*****************************************************************************

static int set_time() {
    long retVal;

    g_time.tm_day = DATE;
    g_time.tm_mon = MONTH;
    g_time.tm_year = YEAR;
    g_time.tm_sec = HOUR;
    g_time.tm_hour = MINUTE;
    g_time.tm_min = SECOND;

    retVal = sl_DevSet(SL_DEVICE_GENERAL_CONFIGURATION,
                          SL_DEVICE_GENERAL_CONFIGURATION_DATE_TIME,
                          sizeof(SlDateTime),(unsigned char *)(&g_time));

    ASSERT_ON_ERROR(retVal);
    return SUCCESS;
}

//*****************************************************************************
//
//! This function demonstrates how certificate can be used with SSL.
//! The procedure includes the following steps:
//! 1) connect to an open AP
//! 2) get the server name via a DNS request
//! 3) define all socket options and point to the CA certificate
//! 4) connect to the server via TCP
//!
//! \param None
//!
//! \return  0 on success else error code
//! \return  LED1 is turned solid in case of success
//!    LED2 is turned solid in case of failure
//!
//*****************************************************************************
static int tls_connect() {
    SlSockAddrIn_t    Addr;
    int    iAddrSize;
    unsigned char ucMethod = SL_SO_SEC_METHOD_TLSV1_2;
//    unsigned int uiCipher = SL_SEC_MASK_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA;
    unsigned int uiIP,uiCipher = SL_SEC_MASK_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA;
// SL_SEC_MASK_SSL_RSA_WITH_RC4_128_SHA
// SL_SEC_MASK_SSL_RSA_WITH_RC4_128_MD5
// SL_SEC_MASK_TLS_RSA_WITH_AES_256_CBC_SHA
// SL_SEC_MASK_TLS_DHE_RSA_WITH_AES_256_CBC_SHA
// SL_SEC_MASK_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
// SL_SEC_MASK_TLS_ECDHE_RSA_WITH_RC4_128_SHA
// SL_SEC_MASK_TLS_RSA_WITH_AES_128_CBC_SHA256
// SL_SEC_MASK_TLS_RSA_WITH_AES_256_CBC_SHA256
// SL_SEC_MASK_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
// SL_SEC_MASK_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256 // does not work (-340, handshake fails)
    long lRetVal = -1;
    int iSockID;

    lRetVal = sl_NetAppDnsGetHostByName(g_Host, strlen((const char *)g_Host),
                                    (unsigned long*)&uiIP, SL_AF_INET);

    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't retrieve the host name \n\r", lRetVal);
    }

    Addr.sin_family = SL_AF_INET;
    Addr.sin_port = sl_Htons(GOOGLE_DST_PORT);
    Addr.sin_addr.s_addr = sl_Htonl(uiIP);
    iAddrSize = sizeof(SlSockAddrIn_t);
    //
    // opens a secure socket
    //
    iSockID = sl_Socket(SL_AF_INET,SL_SOCK_STREAM, SL_SEC_SOCKET);
    if( iSockID < 0 ) {
        return printErrConvenience("Device unable to create secure socket \n\r", lRetVal);
    }

    //
    // configure the socket as TLS1.2
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, SL_SO_SECMETHOD, &ucMethod,\
                               sizeof(ucMethod));
    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }
    //
    //configure the socket as ECDHE RSA WITH AES256 CBC SHA
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, SL_SO_SECURE_MASK, &uiCipher,\
                           sizeof(uiCipher));
    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }



/////////////////////////////////
// START: COMMENT THIS OUT IF DISABLING SERVER VERIFICATION
    //
    //configure the socket with CA certificate - for server verification
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, \
                           SL_SO_SECURE_FILES_CA_FILE_NAME, \
                           SL_SSL_CA_CERT, \
                           strlen(SL_SSL_CA_CERT));

    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }
// END: COMMENT THIS OUT IF DISABLING SERVER VERIFICATION
/////////////////////////////////


    //configure the socket with Client Certificate - for server verification
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, \
                SL_SO_SECURE_FILES_CERTIFICATE_FILE_NAME, \
                                    SL_SSL_CLIENT, \
                           strlen(SL_SSL_CLIENT));

    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }

    //configure the socket with Private Key - for server verification
    //
    lRetVal = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, \
            SL_SO_SECURE_FILES_PRIVATE_KEY_FILE_NAME, \
            SL_SSL_PRIVATE, \
                           strlen(SL_SSL_PRIVATE));

    if(lRetVal < 0) {
        return printErrConvenience("Device couldn't set socket options \n\r", lRetVal);
    }


    /* connect to the peer device - Google server */
    lRetVal = sl_Connect(iSockID, ( SlSockAddr_t *)&Addr, iAddrSize);

    if(lRetVal >= 0) {
        UART_PRINT("Device has connected to the website:");
        UART_PRINT(SERVER_NAME);
        UART_PRINT("\n\r");
    }
    else if(lRetVal == SL_ESECSNOVERIFY) {
        UART_PRINT("Device has connected to the website (UNVERIFIED):");
        UART_PRINT(SERVER_NAME);
        UART_PRINT("\n\r");
    }
    else if(lRetVal < 0) {
        UART_PRINT("Device couldn't connect to server:");
        UART_PRINT(SERVER_NAME);
        UART_PRINT("\n\r");
        return printErrConvenience("Device couldn't connect to server \n\r", lRetVal);
    }

    GPIO_IF_LedOff(MCU_RED_LED_GPIO);
    GPIO_IF_LedOn(MCU_GREEN_LED_GPIO);
    return iSockID;
}



int connectToAccessPoint() {
    long lRetVal = -1;
    GPIO_IF_LedConfigure(LED1|LED3);

    GPIO_IF_LedOff(MCU_RED_LED_GPIO);
    GPIO_IF_LedOff(MCU_GREEN_LED_GPIO);

    lRetVal = InitializeAppVariables();
    ASSERT_ON_ERROR(lRetVal);

    //
    // Following function configure the device to default state by cleaning
    // the persistent settings stored in NVMEM (viz. connection profiles &
    // policies, power policy etc)
    //
    // Applications may choose to skip this step if the developer is sure
    // that the device is in its default state at start of applicaton
    //
    // Note that all profiles and persistent settings that were done on the
    // device will be lost
    //
    lRetVal = ConfigureSimpleLinkToDefaultState();
    if(lRetVal < 0) {
      if (DEVICE_NOT_IN_STATION_MODE == lRetVal)
          UART_PRINT("Failed to configure the device in its default state \n\r");

      return lRetVal;
    }

    UART_PRINT("Device is configured in default state \n\r");

    CLR_STATUS_BIT_ALL(g_ulStatus);

    ///
    // Assumption is that the device is configured in station mode already
    // and it is in its default state
    //
    UART_PRINT("Opening sl_start\n\r");
    lRetVal = sl_Start(0, 0, 0);
    if (lRetVal < 0 || ROLE_STA != lRetVal) {
        UART_PRINT("Failed to start the device \n\r");
        return lRetVal;
    }

    UART_PRINT("Device started as STATION \n\r");

    //
    //Connecting to WLAN AP
    //
    lRetVal = WlanConnect();
    if(lRetVal < 0) {
        UART_PRINT("Failed to establish connection w/ an AP \n\r");
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }

    UART_PRINT("Connection established w/ AP and IP is aquired \n\r");
    return 0;
}

/* =============================== [LAB 4 Functions] ======================================= */

//*****************************************************************************
//
//! Board Initialization & Configuration
//!
//! \param  None
//!
//! \return None
//
//*****************************************************************************
static void BoardInit(void) {
/* In case of TI-RTOS vector table is initialize by OS itself */
#ifndef USE_TIRTOS
  //
  // Set vector table base
  //
#if defined(ccs)
    MAP_IntVTableBaseSet((unsigned long)&g_pfnVectors[0]);
#endif
#if defined(ewarm)
    MAP_IntVTableBaseSet((unsigned long)&__vector_table);
#endif
#endif
    //
    // Enable Processor
    //
    MAP_IntMasterEnable();
    MAP_IntEnable(FAULT_SYSTICK);

    PRCMCC3200MCUInit();
}

//*****************************************************************************
//
//! Main function for spi demo application
//!
//! \param none
//!
//! \return None.
//
//*****************************************************************************
void main()
{
    unsigned long ulStatus;
    BoardInit();
    PinMuxConfig();

    MAP_PRCMPeripheralClkEnable(PRCM_GSPI,PRCM_RUN_MODE_CLK);
    InitTerm();   // Init UART Terminal
    ClearTerm();  // Clear UART Terminal

    //
    // Display the Banner
    //
    Message("\n\n\n\r");
    Message("********************************************\n\r");
    Message("       SwivelFind (EEC 172 Final Proj)      \n\n\r");
    Message("       By: Corbin Warmbier                  \n\r");
    Message("       By: Akhil Sharma                     \n\r");
    Message("       Rev: March 12th, 2024                \n\r");
    Message("********************************************\n\r");
    Message("\n\n\n\r");

    Message("===[Starting Setup Routine]===\n\r");

    MAP_PRCMPeripheralReset(PRCM_GSPI);  // Reset Peripheral
    SysTickInit();  // Enable SysTick


    MAP_GPIOIntRegister(GPIOA0_BASE, GPIOA0IntHandler);            // Register Interrupt Handlers on GPIOA0
    MAP_GPIOIntTypeSet(IR_in.port, IR_in.pin, GPIO_FALLING_EDGE);  // Setup Rising Edge Interrupts on IR_in
    ulStatus = MAP_GPIOIntStatus (IR_in.port, false);
    MAP_GPIOIntClear(IR_in.port, ulStatus);                        // clear interrupts on GPIOA0
    IR_intflag = 0;                                                // clear Global IR interrupt flag

    MAP_GPIOIntEnable(IR_in.port, IR_in.pin);                      // enable interrupts on IR_in pin

    Message(" + Interrupts Enabled [X] \n\r");

    //
    // Reset SPI
    //
    MAP_SPIReset(GSPI_BASE);

    //
    // Configure SPI interface
    //
    MAP_SPIConfigSetExpClk(GSPI_BASE,MAP_PRCMPeripheralClockGet(PRCM_GSPI),
                     SPI_IF_BIT_RATE,SPI_MODE_MASTER,SPI_SUB_MODE_0,
                     (SPI_SW_CTRL_CS |
                     SPI_4PIN_MODE |
                     SPI_TURBO_OFF |
                     SPI_CS_ACTIVEHIGH |
                     SPI_WL_8));

    //
    // Enable SPI for communication
    //
    MAP_SPIEnable(GSPI_BASE);
    Message(" + SPI Enabled [X] \n\r");
    //Connect the CC3200 to the local access point
    lRetVal = connectToAccessPoint();
    //Set time so that encryption can be used
    lRetVal = set_time();
    if(lRetVal < 0) {
        UART_PRINT("Unable to set time in the device");
        LOOP_FOREVER();
    }
    //Connect to the website with TLS encryption
    lRetVal = tls_connect();
    if(lRetVal < 0) {
        ERR_PRINT(lRetVal);
    }
    Message(" + Connected to AWS [X] \n\r");

    // Init OLED and Clear Screen
    Adafruit_Init();
    fillScreen(BLACK);
    printHeader();

    Message(" + OLED Enabled [X] \n\r");

    // Do Initial Setups
    g_ulBase = TIMERA0_BASE;
    Timer_IF_Init(PRCM_TIMERA0, g_ulBase, TIMER_CFG_PERIODIC, TIMER_A, 0);
    Timer_IF_IntSetup(g_ulBase, TIMER_A, TimerBaseIntHandler);

    Message(" + Timers Enabled [X] \n\r");
    Message("===[Setup Routine Complete]===\n\n\r");
    Message("===[Starting Program]===\n\r");

    SysTickReset();
    while (1) {
        while (IR_intflag==0) {;}
        if (IR_intflag) {
            IR_intflag=0;  // clear flag
        }
    }

}

static int http_post(int iTLSSockID){
    char acSendBuff[512];
    char acRecvbuff[3000];//1460
    char cCLLength[200];
    char* pcBufHeaders;
    int lRetVal = 0;

    pcBufHeaders = acSendBuff;
    strcpy(pcBufHeaders, POSTHEADER);
    pcBufHeaders += strlen(POSTHEADER);
    strcpy(pcBufHeaders, HOSTHEADER);
    pcBufHeaders += strlen(HOSTHEADER);
    strcpy(pcBufHeaders, CHEADER);
    pcBufHeaders += strlen(CHEADER);
    strcpy(pcBufHeaders, "\r\n\r\n");

    int dataLength = strlen(DATA1);

    strcpy(pcBufHeaders, CTHEADER);
    pcBufHeaders += strlen(CTHEADER);
    strcpy(pcBufHeaders, CLHEADER1);

    pcBufHeaders += strlen(CLHEADER1);
    sprintf(cCLLength, "%d", dataLength);

    strcpy(pcBufHeaders, cCLLength);
    pcBufHeaders += strlen(cCLLength);
    strcpy(pcBufHeaders, CLHEADER2);
    pcBufHeaders += strlen(CLHEADER2);

    strcpy(pcBufHeaders, DATA1);
    pcBufHeaders += strlen(DATA1);

    int testDataLength = strlen(pcBufHeaders);

    UART_PRINT(acSendBuff);


    //
    // Send the packet to the server */
    //
    UART_PRINT("SSockID before send= %d\n\r", iTLSSockID);
    lRetVal = sl_Send(iTLSSockID, acSendBuff, strlen(acSendBuff), 0);
    UART_PRINT("Sent value, attempting to return, lRetVal = %i\n\r", lRetVal);
    if(lRetVal < 0) {
        UART_PRINT("POST failed. Error Number: %i\n\r",lRetVal);
        sl_Close(iTLSSockID);
        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
        return lRetVal;
    }
    UART_PRINT("Attempting to receive\n\r");
    UART_PRINT("SSockID before recv= %d\n\r", iTLSSockID);
//    lRetVal = sl_Recv(iTLSSockID, &acRecvbuff[0], sizeof(acRecvbuff), 0);
//
//    if(lRetVal < 0) {
//        UART_PRINT("Received failed. Error Number: %i\n\r",lRetVal);
//        //sl_Close(iSSLSockID);
//        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
//        return lRetVal;
//    }
//    else {
//        acRecvbuff[lRetVal+1] = '\0';
//        UART_PRINT(acRecvbuff);
//        UART_PRINT("\n\r\n\r");
//    }

    return 0;
}

//static int http_get(int iTLSSockID) {
//    char acSendBuff[512]; // Buffer for the send data
//    char acRecvbuff[1460]; // Buffer to receive data from the server
//    char cCLLength[200];
//    char* pcBufHeaders; // Pointer to navigate the send buffer
//    int lRetVal = 0; // Return value
//
//    // Initialize the send buffer with the GET request headers
//    pcBufHeaders = acSendBuff;
//    strcpy(pcBufHeaders, GETHEADER); // Assume GETHEADER is defined elsewhere
//    pcBufHeaders += strlen(GETHEADER);
//    strcpy(pcBufHeaders, HOSTHEADER); // Use the same HOSTHEADER as for POST
//    pcBufHeaders += strlen(HOSTHEADER);
//    strcpy(pcBufHeaders, "\r\n"); // End of headers
//
//    int dataLength = strlen(DATA1);
//
//    strcpy(pcBufHeaders, CTHEADER);
//    pcBufHeaders += strlen(CTHEADER);
//    strcpy(pcBufHeaders, CLHEADER1);
//
//    pcBufHeaders += strlen(CLHEADER1);
//    sprintf(cCLLength, "%d", dataLength);
//
//    strcpy(pcBufHeaders, cCLLength);
//    pcBufHeaders += strlen(cCLLength);
//    strcpy(pcBufHeaders, CLHEADER2);
//    pcBufHeaders += strlen(CLHEADER2);
//
//    strcpy(DATA1, DATA_A);
//    DATA1 += strlen(DATA_A);
//    strcpy(DATA1, DATA_B);
//    DATA1 += strlen(DATA_B);
//    strcpy(DATA1, DATA_C);
//    DATA1 += strlen(DATA_C);
//
//    strcpy(pcBufHeaders, DATA1);
//    pcBufHeaders += strlen(DATA1);
//
//    int testDataLength = strlen(pcBufHeaders);
//
//    // Debug print the HTTP GET request
//    UART_PRINT(acSendBuff);
//
//    // Send the GET request to the server
//    lRetVal = sl_Send(iTLSSockID, acSendBuff, strlen(acSendBuff), 0);
//    if (lRetVal < 0) {
//        UART_PRINT("GET failed. Error Number: %i\n\r", lRetVal);
//        sl_Close(iTLSSockID);
//        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
//        return lRetVal;
//    }
//
//    // Receive the response from the server
//    lRetVal = sl_Recv(iTLSSockID, &acRecvbuff[0], sizeof(acRecvbuff), 0);
//    //UART_PRINT("Acrecbuf = %d, lRetVal after sl_recv called = %i\n\r", sizeof(acRecvbuff), lRetVal);
//    if (lRetVal < 0) {
//        UART_PRINT("Receive failed. Error Number: %i\n\r", lRetVal);
//        GPIO_IF_LedOn(MCU_RED_LED_GPIO);
//        return lRetVal;
//    } else {
//        acRecvbuff[lRetVal] = '\0'; // Ensure null-termination
//        UART_PRINT(acRecvbuff);
//        UART_PRINT("\n\r\n\r");
//    }
//
//    return 0;
//}
