module top_module_sva (
    input  logic        clk,
    input  logic        reset,
    input  logic [7:0]  data,
    input  logic [1:0]  shift,
    input  logic        load,
    input  logic [7:0]  q
);

    // Helper: same barrel shift as RTL
    function automatic logic [7:0] barrel8 (input logic [7:0] d, input logic [1:0] s);
        barrel8 = (s[1]) ? {d[0], d[7:1]} :
                  (s[0]) ? {d[1:0], d[7:2]} :
                           {d[2:0], d[7:3]};
    endfunction

    // Helper: rotate-left by 1
    function automatic logic [7:0] rotl8 (input logic [7:0] a);
        rotl8 = {a[6:0], a[7]};
    endfunction

    // Combinational shifted_data computed from top-level inputs
    logic [7:0] sh_now;
    assign sh_now = barrel8(data, shift);

    // Derive current shift register content from q and shifted_data (q = sh_now + sr_now)
    logic [7:0] sr_now;
    assign sr_now = q - sh_now;

    // On load, next shift register equals previous shifted_data.
    check_sr_update_on_load: assert property (
        @(posedge clk) disable iff (reset)
            $past(load) |-> (sr_now == $past(sh_now))
    );

    // Without load, next shift register is previous value rotated left by 1.
    check_sr_rotate_when_no_load: assert property (
        @(posedge clk) disable iff (reset)
            !$past(load) |-> (sr_now == rotl8($past(q) - $past(sh_now)))
    );

    // After load, q equals current shifted_data plus previous shifted_data.
    check_q_next_after_load: assert property (
        @(posedge clk) disable iff (reset)
            $past(load) |-> (q == (sh_now + $past(sh_now)))
    );

    // Without load, q equals current shifted_data plus rotated previous shift register.
    check_q_next_after_no_load: assert property (
        @(posedge clk) disable iff (reset)
            !$past(load) |-> (q == (sh_now + rotl8($past(q) - $past(sh_now))))
    );

    // Two consecutive no-load cycles rotate the shift register twice.
    check_sr_double_rotate_two_no_loads: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(load,2) && !$past(load,1)) |-> (sr_now == rotl8(rotl8($past(q,2) - $past(sh_now,2))))
    );

    // Load followed by no-load rotates the captured shifted_data once.
    check_sr_load_then_rotate: assert property (
        @(posedge clk) disable iff (reset)
            ($past(load,2) && !$past(load,1)) |-> (sr_now == rotl8($past(sh_now,2)))
    );

    // Two consecutive loads make the shift register equal last cycle's shifted_data.
    check_sr_two_consecutive_loads: assert property (
        @(posedge clk) disable iff (reset)
            ($past(load,2) && $past(load,1)) |-> (sr_now == $past(sh_now,1))
    );

    // Eight no-load cycles return the shift register to its original value.
    check_sr_invariant_after_eight_rotates: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(load,1) && !$past(load,2) && !$past(load,3) && !$past(load,4) &&
             !$past(load,5) && !$past(load,6) && !$past(load,7) && !$past(load,8))
            |-> (sr_now == $past(sr_now,8))
    );

    // After eight no-load cycles, q delta equals shifted_data delta (sr returns to original).
    check_q_delta_matches_shifted_delta_after_eight_rotates: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(load,1) && !$past(load,2) && !$past(load,3) && !$past(load,4) &&
             !$past(load,5) && !$past(load,6) && !$past(load,7) && !$past(load,8))
            |-> ((q - $past(q,8)) == (sh_now - $past(sh_now,8)))
    );

    // Two consecutive no-load cycles: q equals current shifted_data plus double-rotated previous sr.
    check_q_after_two_no_loads: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(load,2) && !$past(load,1)) |-> (q == (sh_now + rotl8(rotl8($past(q,2) - $past(sh_now,2)))))
    );

endmodule