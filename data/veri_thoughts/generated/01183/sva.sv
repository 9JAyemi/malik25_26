module full_adder_sva (
    input logic A,
    input logic B,
    input logic Cin,
    input logic Sum,
    input logic Cout
);
    ///// Functional equivalence /////
    // Sum equals A ^ B ^ Cin.
    check_sum_is_xor: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
            Sum == (A ^ B ^ Cin)
    );
    // Cout equals (A & B) | (Cin & (A ^ B)).
    check_cout_definition: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
            Cout == ((A & B) | (Cin & (A ^ B)))
    );

    ///// Truth table /////
    // For A,B,Cin=000 => Sum=0, Cout=0.
    check_tt_000: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
            ((A===1'b0) && (B===1'b0) && (Cin===1'b0)) |-> ((Sum===1'b0) && (Cout===1'b0))
    );
    // For A,B,Cin=100 => Sum=1, Cout=0.
    check_tt_100: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
            ((A===1'b1) && (B===1'b0) && (Cin===1'b0)) |-> ((Sum===1'b1) && (Cout===1'b0))
    );
    // For A,B,Cin=010 => Sum=1, Cout=0.
    check_tt_010: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
            ((A===1'b0) && (B===1'b1) && (Cin===1'b0)) |-> ((Sum===1'b1) && (Cout===1'b0))
    );
    // For A,B,Cin=001 => Sum=1, Cout=0.
    check_tt_001: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
            ((A===1'b0) && (B===1'b0) && (Cin===1'b1)) |-> ((Sum===1'b1) && (Cout===1'b0))
    );
    // For A,B,Cin=110 => Sum=0, Cout=1.
    check_tt_110: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
            ((A===1'b1) && (B===1'b1) && (Cin===1'b0)) |-> ((Sum===1'b0) && (Cout===1'b1))
    );
    // For A,B,Cin=101 => Sum=0, Cout=1.
    check_tt_101: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
            ((A===1'b1) && (B===1'b0) && (Cin===1'b1)) |-> ((Sum===1'b0) && (Cout===1'b1))
    );
    // For A,B,Cin=011 => Sum=0, Cout=1.
    check_tt_011: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
            ((A===1'b0) && (B===1'b1) && (Cin===1'b1)) |-> ((Sum===1'b0) && (Cout===1'b1))
    );
    // For A,B,Cin=111 => Sum=1, Cout=1.
    check_tt_111: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Cin or negedge Cin)
            ((A===1'b1) && (B===1'b1) && (Cin===1'b1)) |-> ((Sum===1'b1) && (Cout===1'b1))
    );
endmodule