module shift_register_sva (
    input logic        clk,
    input logic        load,
    input logic [63:0] data,
    input logic [63:0] q
);
    // q retains the word loaded on the previous load edge until another load edge occurs.
    check_q_holds_previous_loaded_word: assert property (
        @(posedge load) disable iff (1'b0) 1'b1 |=> (q == $past(data))
    );
endmodule