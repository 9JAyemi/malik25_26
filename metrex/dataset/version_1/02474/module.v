
module mux_buffer (
    input wire I0,
    input wire I1,
    input wire S,
    output wire O
);

    assign O = S ? I0: I1;

endmodule