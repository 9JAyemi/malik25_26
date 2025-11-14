
module and_gate (
    input  wire a,
    input  wire b,
    output wire y
);

    wire and_out;

    and (
        and_out,
        a,
        b
    );
    assign y = and_out;

endmodule