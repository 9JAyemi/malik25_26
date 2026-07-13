module DLATCHR_sva (
    input logic D,
    input logic nCLK,
    input logic nRST,
    input logic INIT,
    input logic Q
);

    // nCLK is the clock; nRST is a synchronous active-low reset.

    // Q reflects the input selected on the previous clock edge.
    check_selected_input_function: assert property (
        @(posedge nCLK) disable iff ($initstate)
        1'b1 |=> (Q == $past((!nRST) ? INIT : D))
    );

    // After a non-reset clock edge, the stored value is the previous D.
    check_data_capture: assert property (
        @(posedge nCLK) disable iff ($initstate || !nRST)
        $past(nRST) |-> (Q == $past(D))
    );

    // After a reset clock edge, the reset value is visible once reset releases.
    check_reset_load: assert property (
        @(posedge nCLK) disable iff ($initstate || !nRST)
        $past(!nRST) |-> (Q == $past(INIT))
    );

    // When reset was active and D differed from INIT, Q still comes from INIT.
    check_reset_priority_over_d: assert property (
        @(posedge nCLK) disable iff ($initstate || !nRST)
        $past(!nRST && (D != INIT)) |-> ((Q == $past(INIT)) && (Q != $past(D)))
    );

    // When reset was inactive and D differed from INIT, Q comes from D.
    check_data_path_selected: assert property (
        @(posedge nCLK) disable iff ($initstate || !nRST)
        $past(nRST && (D != INIT)) |-> ((Q == $past(D)) && (Q != $past(INIT)))
    );

endmodule