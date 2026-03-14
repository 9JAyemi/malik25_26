module or3 (
    input A,
    input B,
    input C,
    output X,
    input VPWR,
    input VGND
);

    assign X = A | B | C;

endmodule

module three_input_module (
    input input_a,
    input input_b,
    input input_c,
    output output_x,
    input vpwr,
    input vgnd
);

    wire or1_output;
    wire or2_output;
    wire or3_output;
    
    // instantiate 3-input OR gates
    or3 or1 (
        .A(input_a),
        .B(input_b),
        .C(input_c),
        .X(or1_output),
        .VPWR(vpwr),
        .VGND(vgnd)
    );
    
    or3 or2 (
        .A(input_a),
        .B(input_b),
        .C(or1_output),
        .X(or2_output),
        .VPWR(vpwr),
        .VGND(vgnd)
    );
    
    or3 or3 (
        .A(or2_output),
        .B(input_c),
        .C(or1_output),
        .X(or3_output),
        .VPWR(vpwr),
        .VGND(vgnd)
    );
    
    // invert the output of the final OR gate to get the correct output
    assign output_x = ~or3_output;
    
endmodule