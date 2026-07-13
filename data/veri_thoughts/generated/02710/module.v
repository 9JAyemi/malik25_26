module sync
    (input wire OutputClock,  //
    input  wire reset_b,      //
    input  wire InputData,    //
    output wire OutputData);  //

    
    wire synch_flop_1;
    assign synch_flop_1 = InputData;
    
    
    
    dff_async_reset
        dff_1
        (// Global Signals                  // ----------------------------
        .clk     (OutputClock),
        .reset_b (reset_b),
        //                                  // ----------------------------
        .d       (synch_flop_1),
        .q       (OutputData));
    
endmodule

module dff_async_reset
    (input  wire clk,      //
    input  wire reset_b,  //
    input  wire d,        //
    output reg  q);       //
    
    always @(posedge clk or negedge reset_b) begin
        if (!reset_b) begin
            q <= 0;
        end else begin
            q <= d;
        end
    end
    
endmodule