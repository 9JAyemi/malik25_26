
module and_gate_mux_not (
    input a,
    input b,
    input in,
    output out
);

    wire not_in;

    // NOT gate implementation
    assign not_in = ~in;

    // Multiplexer implementation
    assign out = a ? in: not_in;

endmodule
module priority_encoder (
    input [7:0] in,
    output [2:0] pos
);

    wire [7:0] inv_in;
    wire [7:0] and_out;

    // Inverter implementation
    assign inv_in = ~in;

    // AND gate implementation
    and_gate_mux_not and_gate_0 (
        .a(1'b1),
        .b(1'b1),
        .in(in[0]),
        .out(and_out[0])
    );

    and_gate_mux_not and_gate_1 (
        .a(1'b1),
        .b(1'b1),
        .in(in[1]),
        .out(and_out[1])
    );
    
    and_gate_mux_not and_gate_2 (
        .a(1'b1),
        .b(1'b1),
        .in(in[2]),
        .out(and_out[2])
    );

    and_gate_mux_not and_gate_3 (
        .a(1'b1),
        .b(1'b1),
        .in(in[3]),
        .out(and_out[3])
    );
    
    and_gate_mux_not and_gate_4 (
        .a(1'b1),
        .b(1'b1),
        .in(in[4]),
        .out(and_out[4])
    );

    and_gate_mux_not and_gate_5 (
        .a(1'b1),
        .b(1'b1),
        .in(in[5]),
        .out(and_out[5])
    );
    
    and_gate_mux_not and_gate_6 (
        .a(1'b1),
        .b(1'b1),
        .in(in[6]),
        .out(and_out[6])
    );

    and_gate_mux_not and_gate_7 (
        .a(1'b1),
        .b(1'b1),
        .in(in[7]),
        .out(and_out[7])
    );

    // Priority encoder implementation
    assign pos = {2'b0, and_out[7:6]};

endmodule
module final_module (
    input a,
    input b,
    input [7:0] in,
    output [2:0] pos
);

    wire and_out;
    wire [2:0] priority_pos;

    // AND gate and NOT gate implementation
    and_gate_mux_not and_gate (
        .a(a),
        .b(b),
        .in(in[0]),
        .out(and_out)
    );

    // Priority encoder implementation
    priority_encoder priority_enc (
        .in(in[7:0]),
        .pos(priority_pos)
    );

    // Output assignment
    assign pos = and_out ? priority_pos: 3'b0;

endmodule