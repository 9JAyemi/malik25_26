
module top_module (
    input clk,              // Clock input
    input reset,            // Synchronous active-high reset
    input [7:0] data_in,    // 8-bit input data
    input [2:0] sel,        // 3-bit select input for choosing operation
    output wire [3:0] q          // 4-bit final output
);

    // Declare internal wires for intermediate values
    wire [3:0] q_shifted;      // Result of barrel shift operation
    wire [3:0] q_decoded;      // Result of decoder with enable operation

    // Barrel shift module
    // Shift amount is determined by sel[2] and sel[1:0]
    // (1, 2, or no shift)
    wire [2:0] shift_amount = {sel[2], sel[1:0]}; // Added braces for clarity

    // Barrel Shifter module `bs`
    // Connect the wires to the module ports
    barrel_shifter bs (
        .clk(clk),
        .reset(reset),
        .data_in(data_in),
        .shift_sel(sel[2:1]), // sel[2:1] is used for shift_sel
        .shift_amt(shift_amount),
        .shift_out(q_shifted)
    );

    // Decoder with enable module
    // Enable is determined by sel[2], and data_in is the decoded value
    decoder_with_enable dwen (
        .data_in(data_in),
        .enable(sel[2]),
        .decode_out(q_decoded)
    );

    // Bitwise OR module
    // `a` is the result of the barrel shift operation(`q_shifted`),
    // and `b` is the result of the decoder with enable operation(`q_decoded`)
    bitwise_or bo (
        .a(q_shifted),
        .b(q_decoded),
        .or_out(q)
    );

endmodule

module barrel_shifter (
    input clk,              // Clock input
    input reset,            // Synchronous active-high reset
    input [7:0] data_in,    // 8-bit input data
    input [1:0] shift_sel,  // 2-bit select input for choosing shift direction
    input [2:0] shift_amt,  // 3-bit select input for choosing shift amount
    output reg [3:0] shift_out  // 4-bit shifted output
);

    reg [7:0] shift_reg;    // Shift register

    always @(posedge clk) begin
        if (reset) begin
            shift_reg <= 8'b0;
        end else begin
            case (shift_sel)
                2'b00: shift_reg <= shift_reg; // No shift
                2'b01: shift_reg <= {shift_reg[6:0], 1'b0}; // Shift left by 1
                2'b10: shift_reg <= {1'b0, shift_reg[7:1]}; // Shift right by 1
                2'b11: begin // Shift right by 2
                    shift_reg <= {2'b00, shift_reg[7:2]};
                end
            endcase

            case (shift_amt)
                3'b000: shift_out <= shift_reg[3:0]; // No shift
                3'b001: shift_out <= shift_reg[4:1]; // Shift left by 1
                3'b010: shift_out <= shift_reg[5:2]; // Shift right by 1
                3'b011: shift_out <= shift_reg[6:3]; // Shift right by 2
                default: shift_out <= 4'bxxxx; // Invalid shift amount
            endcase
        end
    end

endmodule

module decoder_with_enable (
    input [7:0] data_in,    // 8-bit input data
    input enable,            // Enable input
    output reg [3:0] decode_out  // 4-bit decoded output
);

    always @(data_in, enable) begin
        if (enable) begin
            case (data_in[7:6])
                2'b00: decode_out <= 4'b0000;
                2'b01: decode_out <= 4'b0001;
                2'b10: decode_out <= 4'b0010;
                2'b11: decode_out <= 4'b0011;
            endcase
        end else begin
            case (data_in[5:4])
                2'b00: decode_out <= 4'b0100;
                2'b01: decode_out <= 4'b0101;
                2'b10: decode_out <= 4'b0110;
                2'b11: decode_out <= 4'b0111;
            endcase
        end
    end

endmodule

module bitwise_or (
    input [3:0] a,          // 4-bit input a
    input [3:0] b,          // 4-bit input b
    output wire [3:0] or_out // 4-bit bitwise OR output
);

    assign or_out = a | b;

endmodule
