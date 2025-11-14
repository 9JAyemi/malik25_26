module nor_logic(
    input [3:0] in,
    output out_and,
    output out_or,
    output out_xor
);

    wire [3:0] neg_in;
    assign neg_in = ~in;

    // Output for AND operation
    assign out_and = ~(neg_in[0] | neg_in[1] | neg_in[2] | neg_in[3]);

    // Output for OR operation
    assign out_or = ~(in[0] | in[1] | in[2] | in[3]);

    // Output for XOR operation
    assign out_xor = ~(in[0] ^ neg_in[0] ^ in[1] ^ neg_in[1] ^ in[2] ^ neg_in[2] ^ in[3] ^ neg_in[3]);

endmodule

module control_logic(
    input select,
    output [1:0] active_output
);

    // Output selection logic
    assign active_output = (select == 1'b0) ? 2'b10 : 2'b01;

endmodule

module top_module( 
    input [3:0] in,
    input select,
    output out_and,
    output out_or,
    output out_xor,
    output [1:0] active_output
);

    wire out_and_nor, out_or_nor, out_xor_nor;

    // NOR logic module instantiation
    nor_logic nor_inst(
        .in(in),
        .out_and(out_and_nor),
        .out_or(out_or_nor),
        .out_xor(out_xor_nor)
    );

    // Control logic module instantiation
    control_logic control_inst(
        .select(select),
        .active_output(active_output)
    );

    // Output selection logic
    assign {out_and, out_or, out_xor} = (active_output == 2'b10) ? {out_and_nor, 1'b0, 1'b0} : {1'b0, out_or_nor, out_xor_nor};

endmodule