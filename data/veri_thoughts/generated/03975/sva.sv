module OverallController_sva (
    input logic Clock,
    input logic IncrementData,
    input logic LoadData,
    input logic Reset,
    input logic AddOne,
    input logic WriteOrRead
);

    // Increment requests decode to increment outputs on the next cycle.
    check_increment_request_to_increment_outputs: assert property (
        @(posedge Clock) disable iff (Reset)
        IncrementData |=> (AddOne && WriteOrRead)
    );

    // Load-only requests decode to load outputs on the next cycle.
    check_load_only_request_to_load_outputs: assert property (
        @(posedge Clock) disable iff (Reset)
        (!IncrementData && LoadData) |=> (!AddOne && WriteOrRead)
    );

    // No request decodes to read outputs on the next cycle.
    check_no_request_to_read_outputs: assert property (
        @(posedge Clock) disable iff (Reset)
        (!IncrementData && !LoadData) |=> (!AddOne && !WriteOrRead)
    );

    // IncrementData has priority when both requests are asserted.
    check_increment_priority_over_load: assert property (
        @(posedge Clock) disable iff (Reset)
        (IncrementData && LoadData) |=> (AddOne && WriteOrRead)
    );

    // Any request drives WriteOrRead high on the next cycle.
    check_request_sets_writeorread: assert property (
        @(posedge Clock) disable iff (Reset)
        (IncrementData || LoadData) |=> WriteOrRead
    );

    // AddOne is never asserted without WriteOrRead.
    check_addone_implies_writeorread: assert property (
        @(posedge Clock) disable iff (Reset)
        AddOne |-> WriteOrRead
    );

    // After reset is released, outputs still reflect the initial decode.
    check_outputs_idle_after_reset_release: assert property (
        @(posedge Clock) disable iff (Reset)
        $fell(Reset) |-> (!AddOne && !WriteOrRead)
    );

endmodule