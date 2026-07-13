
module xor_module (
    input a, // 1-bit binary input a
    input b, // 1-bit binary input b
    output wire out_comb // 1-bit binary output
);

    assign out_comb = a ^ b;

endmodule

module mux_module (
    input [1:0] select, // select input
    input [2:0] mux_in, // 3-bit binary input
    output wire [3:0] mux_out // 4-bit binary output
);

    assign mux_out = (select == 2'b00) ? {1'b0, mux_in[2:1]} :
                     (select == 2'b01) ? {1'b0, mux_in[1:0], 1'b0} :
                     (select == 2'b10) ? {mux_in[2], 1'b0, mux_in[0]} :
                     {mux_in[2:0], 1'b0};

endmodule

module top_module (
    input clk, // clock input
    input a, // 1-bit binary input a for XOR module
    input b, // 1-bit binary input b for XOR module
    input [1:0] select, // select input for multiplexer
    input [2:0] mux_in, // 3-bit binary input for multiplexer
    output wire out_comb_ff, // 1-bit binary output for XOR module
    output wire [3:0] mux_out, // 4-bit binary output for multiplexer
    output reg out_final // 1-bit binary output for final result
);

    xor_module xor_inst (
        .a(a),
        .b(b),
        .out_comb(out_comb_ff)
    );

    mux_module mux_inst (
        .select(select),
        .mux_in(mux_in),
        .mux_out(mux_out)
    );

    always @ (posedge clk)
    begin
        case (mux_out)
            4'b0001: out_final <= out_comb_ff; // output 0th bit
            4'b0010: out_final <= ~out_comb_ff; // output 1st bit
            4'b0100: out_final <= 1'b0; // output 2nd bit
            4'b1000: out_final <= 1'b1; // output 3rd bit
        endcase
    end

endmodule
