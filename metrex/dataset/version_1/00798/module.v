
module waveform_generator(
    output reg Y,
    input A1,
    input A2,
    input B1
);

    // Internal signal
    wire Y_internal;

    // Instantiate an A21OI gate
    sky130_fd_sc_hdll__a21oi_2 U1(
        .Y(Y_internal),
        .A1(A1),
        .A2(A2),
        .B1(B1)
    );

    // Register update logic
    always @(posedge B1) begin
        Y <= Y_internal;
    end

endmodule
module sky130_fd_sc_hdll__a21oi_2 (
    output Y,
    input A1,
    input A2,
    input B1
);

    // Instantiate an A21OI gate
    assign Y = A1 & A2 | B1;

endmodule