module top_module_sva (
    input logic a, b, cin,
    input logic cout, sum,
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [3:0] out
);
    // Full adder sum equals XOR of inputs.
    fa_sum_eq_xor: assert property (
        @(posedge $global_clock) sum == (a ^ b ^ cin)
    );
    // Full adder carry-out equals majority of inputs.
    fa_cout_eq_majority: assert property (
        @(posedge $global_clock) cout == ((a & b) | (a & cin) | (b & cin))
    );

    // For sel==0, final out equals data0 + {cout,sum}.
    final_out_sel0: assert property (
        @(posedge $global_clock) (sel == 3'b000) |-> (out == (data0 + {cout, sum}))
    );
    // For sel==1, final out equals data1 + {cout,sum}.
    final_out_sel1: assert property (
        @(posedge $global_clock) (sel == 3'b001) |-> (out == (data1 + {cout, sum}))
    );
    // For sel==2, final out equals data2 + {cout,sum}.
    final_out_sel2: assert property (
        @(posedge $global_clock) (sel == 3'b010) |-> (out == (data2 + {cout, sum}))
    );
    // For sel==3, final out equals data3 + {cout,sum}.
    final_out_sel3: assert property (
        @(posedge $global_clock) (sel == 3'b011) |-> (out == (data3 + {cout, sum}))
    );
    // For sel==4, final out equals data4 + {cout,sum}.
    final_out_sel4: assert property (
        @(posedge $global_clock) (sel == 3'b100) |-> (out == (data4 + {cout, sum}))
    );
    // For sel==5, final out equals data5 + {cout,sum}.
    final_out_sel5: assert property (
        @(posedge $global_clock) (sel == 3'b101) |-> (out == (data5 + {cout, sum}))
    );

    // For illegal sel (6 or 7), final out must be unknown due to mux default Xs.
    final_out_illegal_sel_unknown: assert property (
        @(posedge $global_clock) (sel inside {3'b110,3'b111}) |-> $isunknown(out)
    );
    // Unknown sel drives mux default, so final out must be unknown.
    final_out_unknown_when_sel_unknown: assert property (
        @(posedge $global_clock) $isunknown(sel) |-> $isunknown(out)
    );

    // Full adder outputs are known when inputs are 2-state.
    fa_outputs_known_when_inputs_known: assert property (
        @(posedge $global_clock) (!$isunknown({a,b,cin})) |-> (!$isunknown(sum) && !$isunknown(cout))
    );

    // Final out is known when selected data and {cout,sum} are 2-state.
    final_out_known_when_selected_known: assert property (
        @(posedge $global_clock)
        (
            (sel == 3'b000 && !$isunknown({data0,cout,sum})) ||
            (sel == 3'b001 && !$isunknown({data1,cout,sum})) ||
            (sel == 3'b010 && !$isunknown({data2,cout,sum})) ||
            (sel == 3'b011 && !$isunknown({data3,cout,sum})) ||
            (sel == 3'b100 && !$isunknown({data4,cout,sum})) ||
            (sel == 3'b101 && !$isunknown({data5,cout,sum}))
        ) |-> !$isunknown(out)
    );

    // Final out is unknown if selected data or {cout,sum} is unknown.
    final_out_unknown_when_selected_unknown: assert property (
        @(posedge $global_clock)
        (
            (sel == 3'b000 && ($isunknown(data0) || $isunknown({cout,sum}))) ||
            (sel == 3'b001 && ($isunknown(data1) || $isunknown({cout,sum}))) ||
            (sel == 3'b010 && ($isunknown(data2) || $isunknown({cout,sum}))) ||
            (sel == 3'b011 && ($isunknown(data3) || $isunknown({cout,sum}))) ||
            (sel == 3'b100 && ($isunknown(data4) || $isunknown({cout,sum}))) ||
            (sel == 3'b101 && ($isunknown(data5) || $isunknown({cout,sum})))
        ) |-> $isunknown(out)
    );
endmodule