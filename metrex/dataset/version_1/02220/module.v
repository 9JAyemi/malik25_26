module top_module (
    input [3:0] in,
    output reg [3:0] out
);

    // Instantiate the barrel shifter module
    barrel_shifter bs(
        .data(in),
        .shift(1),
        .out(wire_bs_out)
    );
    
    // Instantiate the two's complement module
    twos_complement tc(
        .in(wire_bs_out),
        .out(out)
    );

    // Declare wire for output of barrel shifter module
    wire [3:0] wire_bs_out;

endmodule

// Barrel shifter module
module barrel_shifter (
    input [3:0] data,
    input [1:0] shift,
    output reg [3:0] out
);

    always @(*) begin
        case(shift)
            2'b00: out = data; // No shift
            2'b01: out = {data[2:0], data[3]}; // Rotate left by 1 bit
            2'b10: out = {data[1:0], data[3:2]}; // Rotate left by 2 bits
            2'b11: out = {data[0], data[3:1]}; // Rotate left by 3 bits
        endcase
    end

endmodule

// Two's complement module
module twos_complement (
    input [3:0] in,
    output reg [3:0] out
);

    always @(*) begin
        out = ~in + 1;
    end

endmodule