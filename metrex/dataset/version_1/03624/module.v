module top_module (
    input [3:0] A,
    input [3:0] B,
    input select,
    input subtract,
    output eq,
    output gt,
    output [3:0] result
);

    wire [3:0] adder_out;
    wire [3:0] comparator_out;
    wire [3:0] final_result;

    // Instantiate adder/subtractor module
    adder_subtractor add_sub (
        .A(A),
        .B(B),
        .subtract(subtract),
        .result(adder_out)
    );

    // Instantiate magnitude comparator module
    magnitude_comparator mag_comp (
        .A(A),
        .B(B),
        .eq(eq),
        .gt(gt),
        .result(comparator_out)
    );

    // Functional module to select output
    assign final_result = select ? comparator_out : adder_out;

    // Output signals
    assign result = final_result;

endmodule

// Adder/Subtractor module
module adder_subtractor (
    input [3:0] A,
    input [3:0] B,
    input subtract,
    output [3:0] result
);

    assign result = subtract ? A - B : A + B;

endmodule

// Magnitude Comparator module
module magnitude_comparator (
    input [3:0] A,
    input [3:0] B,
    output eq,
    output gt,
    output [3:0] result
);

    assign eq = (A == B);
    assign gt = (A > B);
    assign result = {gt, eq};

endmodule