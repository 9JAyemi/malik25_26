module top_module(
    input clk,
    input areset,   // async active-high reset to zero
    input [7:0] d,
    input sel,
    input load,
    input ena,
    input [3:0] data,
    output reg [7:0] q
);

    // First module with 8 D flip-flops triggered by negative edge of clk
    reg [7:0] dff_q;
    always @(negedge clk or posedge areset) begin
        if (areset) begin
            dff_q <= 8'b0;
        end else begin
            dff_q <= {dff_q[3:0], dff_q[7:4]};
        end
    end
    
    // Multiplexer to select output of first 4 DFFs or last 4 DFFs based on select input
    wire [3:0] first_half = dff_q[3:0];
    wire [3:0] second_half = dff_q[7:4];
    wire [3:0] mux_out;
    assign mux_out = (sel == 1'b0) ? first_half : second_half;
    
    // Second module with 4-bit shift register with asynchronous reset, synchronous load, and enable
    reg [3:0] shift_reg;
    always @(posedge clk or posedge areset) begin
        if (areset) begin
            shift_reg <= 4'b0;
        end else if (load) begin
            shift_reg <= data;
        end else if (ena) begin
            shift_reg <= {1'b0, shift_reg[3:1]};
        end
    end
    
    // XOR module to combine outputs of the two given modules
    wire [7:0] xor_out;
    assign xor_out = shift_reg ^ mux_out;
    
    // Output of the top module
    always @(posedge clk or posedge areset) begin
        if (areset) begin
            q <= 8'b0;
        end else begin
            q <= xor_out;
        end
    end
    
endmodule