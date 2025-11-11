module binary_counter (
    input clk,
    input reset,      // Asynchronous active-high reset
    output reg [3:0] q);
    
    // Define states
    parameter [1:0]
        S0 = 2'b00,
        S1 = 2'b01,
        S2 = 2'b10,
        S3 = 2'b11;
    
    // Define state register and next state logic
    reg [1:0] state, next_state;
    always @ (posedge clk, posedge reset) begin
        if (reset) begin
            state <= S0;
        end else begin
            state <= next_state;
        end
    end
    
    // Define output logic
    always @ (*) begin
        case (state)
            S0: q = 4'b0000;
            S1: q = 4'b0001;
            S2: q = 4'b0010;
            S3: q = 4'b0011;
        endcase
    end
    
    // Define next state logic
    always @ (*) begin
        case (state)
            S0: next_state = S1;
            S1: next_state = S2;
            S2: next_state = S3;
            S3: next_state = S0;
        endcase
    end
    
endmodule

module top_module (
    input clk,
    input reset,      // Asynchronous active-high reset
    output [3:0] q);
    
    binary_counter counter (
        .clk(clk),
        .reset(reset),
        .q(q)
    );
    
endmodule