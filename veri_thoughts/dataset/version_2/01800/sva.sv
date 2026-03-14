module adder_4bit_sva (
    input logic CLK,          // External clock for assertions (RTL is purely combinational, no reset)
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic enable,
    input logic [3:0] Sum,
    input logic Cout
);

    // Sum muxes between A and (A+B+Cin)[3:0] based on enable.
    check_sum_mux: assert property (
        @(posedge CLK) Sum == (enable ? (A + B + Cin)[3:0] : A)
    );

    // When disabled, Sum equals A.
    check_sum_bypass: assert property (
        @(posedge CLK) !enable |-> (Sum == A)
    );

    // When enabled, Sum equals the low 4 bits of A + B + Cin.
    check_sum_add_low4: assert property (
        @(posedge CLK) enable |-> (Sum == (A + B + Cin)[3:0])
    );

    // Cout equals Cin given comparator implementation.
    check_cout_equals_cin: assert property (
        @(posedge CLK) (Cout == Cin)
    );

    // Cin HIGH implies Cout HIGH.
    check_cout_when_cin_high: assert property (
        @(posedge CLK) Cin |-> (Cout == 1'b1)
    );

    // Cin LOW implies Cout LOW.
    check_cout_when_cin_low: assert property (
        @(posedge CLK) !Cin |-> (Cout == 1'b0)
    );

    // If B==0 and Cin==0, Sum equals A regardless of enable.
    check_sum_identity_when_B0_C0: assert property (
        @(posedge CLK) (B == 4'b0000 && Cin == 1'b0) |-> (Sum == A)
    );

endmodule