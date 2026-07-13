
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [3:0] load, // Input for synchronous parallel load of counter
    input [3:0] IN,   // Input for the barrel shifter
    input [1:0] SHIFT, // Shift amount input for the barrel shifter
    input MODE,        // Mode input for the barrel shifter
    output [3:0] q // Output from the functional module
);

wire [3:0] counter_out;
wire [3:0] shifted_out;

// Instantiate the counter module
counter counter_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .q(counter_out)
);

// Instantiate the barrel shifter module
barrel_shifter shifter_inst (
    .IN(IN),
    .SHIFT(SHIFT),
    .MODE(MODE),
    .q(shifted_out)
);

// Perform logical left shift on the counter output by the shift amount specified in the barrel shifter mode input
assign q = shifted_out << SHIFT;

endmodule

module counter (
    input clk,
    input reset,      // Synchronous active-high reset
    input [3:0] load, // Input for synchronous parallel load of counter
    output reg [3:0] q // Output from the counter
);

always @ (posedge clk) begin
    if (reset) begin
        q <= 0;
    end else if (load) begin
        q <= load;
    end else begin
        q <= q + 1;
    end
end

endmodule

module barrel_shifter (
    input [3:0] IN,   // Input for the barrel shifter
    input [1:0] SHIFT, // Shift amount input for the barrel shifter
    input MODE,        // Mode input for the barrel shifter
    output reg [3:0] q // Output from the barrel shifter
);

always @ (*) begin
    case (MODE)
        2'b00: q = IN >> SHIFT; // Logical right shift
        2'b01: q = IN << SHIFT; // Logical left shift
        2'b10: q = {IN[3], IN[3], IN[3], IN} >> SHIFT; // Arithmetic right shift
        default: q = 0;
    endcase
end

endmodule
