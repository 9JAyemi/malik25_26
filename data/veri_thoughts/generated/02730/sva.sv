module myModule_sva (
    input logic [3:0] v0550b6,
    input logic [3:0] v24708e,
    input logic       v4642b6,
    input logic [3:0] v817794
);

    ///// Counter behavior on v4642b6 clock /////
    // Counter increments by 1 on each rising edge of v4642b6 (checked between consecutive edges).
    check_counter_increments: assert property (
        @(posedge v4642b6) 1'b1 |=> (v817794 == $past(v817794) + 4'd1)
    );
    // If counter is 15 on one edge, it wraps to 0 on the next edge.
    check_counter_wrap: assert property (
        @(posedge v4642b6) (v817794 == 4'hF) |=> (v817794 == 4'h0)
    );

    ///// Combinational select logic for v4642b6 /////
    // When sel=0000, v4642b6 equals v24708e[0].
    check_sel_0000: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b0000) |-> (v4642b6 == v24708e[0])
    );
    // When sel=0001, v4642b6 equals v24708e[1].
    check_sel_0001: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b0001) |-> (v4642b6 == v24708e[1])
    );
    // When sel=0010, v4642b6 equals v24708e[2].
    check_sel_0010: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b0010) |-> (v4642b6 == v24708e[2])
    );
    // When sel=0011, v4642b6 equals v24708e[3].
    check_sel_0011: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b0011) |-> (v4642b6 == v24708e[3])
    );
    // When sel=0100, v4642b6 equals v24708e[0] & v24708e[1].
    check_sel_0100: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b0100) |-> (v4642b6 == (v24708e[0] & v24708e[1]))
    );
    // When sel=0101, v4642b6 equals v24708e[0] & v24708e[2].
    check_sel_0101: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b0101) |-> (v4642b6 == (v24708e[0] & v24708e[2]))
    );
    // When sel=0110, v4642b6 equals v24708e[0] & v24708e[3].
    check_sel_0110: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b0110) |-> (v4642b6 == (v24708e[0] & v24708e[3]))
    );
    // When sel=0111, v4642b6 equals v24708e[1] & v24708e[2].
    check_sel_0111: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b0111) |-> (v4642b6 == (v24708e[1] & v24708e[2]))
    );
    // When sel=1000, v4642b6 equals v24708e[1] & v24708e[3].
    check_sel_1000: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b1000) |-> (v4642b6 == (v24708e[1] & v24708e[3]))
    );
    // When sel=1001, v4642b6 equals v24708e[2] & v24708e[3].
    check_sel_1001: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b1001) |-> (v4642b6 == (v24708e[2] & v24708e[3]))
    );
    // When sel=1010, v4642b6 equals v24708e[0] | v24708e[1].
    check_sel_1010: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b1010) |-> (v4642b6 == (v24708e[0] | v24708e[1]))
    );
    // When sel=1011, v4642b6 equals v24708e[0] | v24708e[2].
    check_sel_1011: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b1011) |-> (v4642b6 == (v24708e[0] | v24708e[2]))
    );
    // When sel=1100, v4642b6 equals v24708e[0] | v24708e[3].
    check_sel_1100: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b1100) |-> (v4642b6 == (v24708e[0] | v24708e[3]))
    );
    // When sel=1101, v4642b6 equals v24708e[1] | v24708e[2].
    check_sel_1101: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b1101) |-> (v4642b6 == (v24708e[1] | v24708e[2]))
    );
    // When sel=1110, v4642b6 equals v24708e[1] | v24708e[3].
    check_sel_1110: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b1110) |-> (v4642b6 == (v24708e[1] | v24708e[3]))
    );
    // When sel=1111, v4642b6 equals v24708e[2] | v24708e[3].
    check_sel_1111: assert property (
        @(posedge v4642b6) (v0550b6 == 4'b1111) |-> (v4642b6 == (v24708e[2] | v24708e[3]))
    );

endmodule