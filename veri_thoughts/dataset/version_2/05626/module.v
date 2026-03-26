module multiplexer #(parameter N = 1) (
    input ctrl,
    input [N-1:0] D0,
    input [N-1:0] D1,
    output [N-1:0] S
);

genvar i;
generate
    for (i = 0; i < N; i = i + 1) begin : mux_loop
        assign S[i] = (ctrl == 1'b0) ? D0[i] : D1[i];
    end
endgenerate

endmodule