
module top_module (
    input clk,
    input reset,
    input select,
    input [15:0] in_A, 
    input [15:0] in_B,
    output reg [7:0] out
);

reg [15:0] reg_in;
wire [15:0] shift_out;
wire [15:0] mux_out;
wire [15:0] and_out;

// Register module
always @(posedge clk, posedge reset) begin
    if (reset) begin
        reg_in <= 16'b0;
    end else begin
        reg_in <= in_A;
    end
end

// Barrel shifter module
assign shift_out = reg_in << select;

// 2-to-1 multiplexer module
reg temp_mux_out; // Use reg instead of wire
always @(select, in_A, in_B) begin
    case (select)
        1'b0: temp_mux_out <= in_A;
        1'b1: temp_mux_out <= in_B;
    endcase
end

assign mux_out = temp_mux_out; // Assign reg to wire

// Functional module
assign and_out = mux_out & shift_out;

// Output register
always @(posedge clk) begin
    out <= and_out[7:0];
end

endmodule
