module sky130_fd_sc_ls__xnor2 (
    input A,
    input B,
    output Y
);

assign Y = ~(A ^ B);

endmodule