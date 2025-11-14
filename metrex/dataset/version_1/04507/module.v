
module OledEX (
        CLK,
        RST,
        EN,
        CS,
        SDO,
        SCLK,
        DC,
        FIN,
        // Position on the screen
        xpos,
        ypos
    );

    // ===========================================================================
    //                                      Port Declarations
    // ===========================================================================
    input CLK;
    input RST;
    input EN;
    output reg CS = 1'b1; // Added initial value to CS
    output reg SDO;
    output reg SCLK = 1'b0; // Added initial value to SCLK
    output reg FIN = 1'b0; // Added initial value to FIN
    input [9:0] xpos;
    input [9:0] ypos;

    // ===========================================================================
    //                              Parameters, Registers, and Wires
    // ===========================================================================

    parameter ExampleReset = 4'b0000, ExampleSendData = 4'b0001, ExampleIdle = 4'b1111;
    reg [3:0] current_state = ExampleReset;

    // ===========================================================================
    //                                      Implementation
    // ===========================================================================

    // Assign outputs that do not change
    output reg DC = 1'b1;

    // State Machine
    // This state machine sends data to the OLED display based on the x and y positions
    always @(posedge CLK) begin
            if(RST == 1'b1) begin
                    current_state <= ExampleReset;
            end
            else if(EN == 1'b1) begin
                    case(current_state)
                            ExampleReset : begin
                                    SDO <= 1'b0;
                                    current_state <= ExampleSendData;
                            end
                            ExampleSendData : begin
                                    SDO <= 1'b1;
                                    // Send data to the OLED display based on the x and y positions
                                    current_state <= ExampleIdle;
                            end
                            ExampleIdle : begin
                                    FIN <= 1'b1;
                            end
                    endcase
            end
    end

endmodule