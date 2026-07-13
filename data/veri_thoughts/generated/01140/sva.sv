module mux32to16_sva (
    input logic [31:0] out,
    input logic [31:0] in1,
    input logic [31:0] in2,
    input logic        control
);
    // When control goes HIGH, out must equal in2.
    select_in2_on_control_high: assert property (
        @(posedge control) out == in2
    );

    // When control goes LOW, out must equal in1.
    select_in1_on_control_low: assert property (
        @(negedge control) out == in1
    );

    // SOP equivalence at control HIGH: out = (~control & in1) | (control & in2).
    sop_equivalence_on_control_high: assert property (
        @(posedge control) out == (({32{~control}} & in1) | ({32{control}} & in2))
    );

    // SOP equivalence at control LOW: out = (~control & in1) | (control & in2).
    sop_equivalence_on_control_low: assert property (
        @(negedge control) out == (({32{~control}} & in1) | ({32{control}} & in2))
    );
endmodule