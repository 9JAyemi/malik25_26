module parameterized_mux #(parameter DATA_WIDTH = 1) (
    input ctrl,
    input [DATA_WIDTH-1:0] D0,
    input [DATA_WIDTH-1:0] D1,
    output [DATA_WIDTH-1:0] S
);

    // Multiplexer logic
    // When ctrl is 0, select D0; when ctrl is 1, select D1.
    assign S = ctrl ? D1 : D0;

endmodule
