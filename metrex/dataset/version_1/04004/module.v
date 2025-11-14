module SmallBpf (
    input clk,         // System clock
    input rst,         // Reset, active high and synchronous
    input en,          // Filter enable
    input signed [WIDTH-1:0] dataIn,  // [WIDTH-1:0] Filter input
    output reg signed [WIDTH-1:0] dataOut  // [WIDTH-1:0] Filter output
);

parameter K0_SHIFT = 5; // K0 filter term = 2^-K0_SHIFT
parameter K1_SHIFT = 5; // K1 filter term = 2^-K1_SHIFT
parameter WIDTH = 16;   // Width of data path
parameter CLAMP = 1;    // Set to 1 to clamp the accumulators

reg signed [WIDTH-1:0] acc0; // First accumulator
reg signed [WIDTH-1:0] acc1; // Second accumulator
reg signed [WIDTH-1:0] acc2; // Third accumulator
reg signed [WIDTH-1:0] acc3; // Fourth accumulator

wire signed [WIDTH-1:0] dataInK0; // dataIn * K0
wire signed [WIDTH-1:0] dataInK1; // dataIn * K1
wire signed [WIDTH-1:0] acc0K0;   // acc0 * K0
wire signed [WIDTH-1:0] acc1K1;   // acc1 * K1
wire signed [WIDTH-1:0] acc2K0;   // acc2 * K0
wire signed [WIDTH-1:0] acc3K1;   // acc3 * K1

// Multiply dataIn by K0 and K1
assign dataInK0 = dataIn << K0_SHIFT;
assign dataInK1 = dataIn << K1_SHIFT;

// Multiply accumulators by K0 and K1
assign acc0K0 = acc0 << K0_SHIFT;
assign acc1K1 = acc1 << K1_SHIFT;
assign acc2K0 = acc2 << K0_SHIFT;
assign acc3K1 = acc3 << K1_SHIFT;

// BPF equations
always @(posedge clk) begin
    if (rst) begin
        acc0 <= 0;
        acc1 <= 0;
        acc2 <= 0;
        acc3 <= 0;
        dataOut <= 0;
    end
    else if (en) begin
        acc0 <= dataInK0 - acc0K0 + acc1K1;
        acc1 <= acc0K0 + acc1K1;
        acc2 <= acc2K0 - acc3K1 + acc1;
        acc3 <= acc3K1 + acc1;
        if (CLAMP) begin
            if (acc0 > (2**(WIDTH-1))-1) acc0 <= (2**(WIDTH-1))-1;
            if (acc0 < -(2**(WIDTH-1))) acc0 <= -(2**(WIDTH-1));
            if (acc1 > (2**(WIDTH-1))-1) acc1 <= (2**(WIDTH-1))-1;
            if (acc1 < -(2**(WIDTH-1))) acc1 <= -(2**(WIDTH-1));
            if (acc2 > (2**(WIDTH-1))-1) acc2 <= (2**(WIDTH-1))-1;
            if (acc2 < -(2**(WIDTH-1))) acc2 <= -(2**(WIDTH-1));
            if (acc3 > (2**(WIDTH-1))-1) acc3 <= (2**(WIDTH-1))-1;
            if (acc3 < -(2**(WIDTH-1))) acc3 <= -(2**(WIDTH-1));
        end
        dataOut <= acc2;
    end
end

endmodule