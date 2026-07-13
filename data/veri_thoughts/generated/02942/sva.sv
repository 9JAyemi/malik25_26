module hazard_sva (
    input logic CLK,

    input logic [2:0] reg_read_adr1_d,
    input logic [2:0] reg_read_adr2_d,
    input logic [2:0] reg_read_adr1_e,
    input logic [2:0] reg_read_adr2_e,
    input logic [2:0] reg_write_adr_e,
    input logic mem_to_reg_e,
    input logic reg_write_m,
    input logic [2:0] reg_write_adr_m,
    input logic reg_write_w,
    input logic [2:0] reg_write_adr_w,
    input logic PC_source,

    input logic stall_f,
    input logic stall_d,
    input logic flush_d,
    input logic flush_e,

    input logic [1:0] forward1_e,
    input logic [1:0] forward2_e
);
    // Forward1: M stage has priority when address matches
    fwd1_from_m_when_match: assert property (
        @(posedge CLK) disable iff (1'b0)
        (reg_write_m && (reg_write_adr_m == reg_read_adr1_e)) |-> (forward1_e == 2'h1)
    );

    // Forward1: W stage selected only if M does not match and W matches
    fwd1_from_w_when_no_m_but_w_match: assert property (
        @(posedge CLK) disable iff (1'b0)
        (! (reg_write_m && (reg_write_adr_m == reg_read_adr1_e)) &&
          (reg_write_w && (reg_write_adr_w == reg_read_adr1_e))) |-> (forward1_e == 2'h2)
    );

    // Forward1: No match in M or W yields no forwarding
    fwd1_none_when_no_matches: assert property (
        @(posedge CLK) disable iff (1'b0)
        (! (reg_write_m && (reg_write_adr_m == reg_read_adr1_e)) &&
         ! (reg_write_w && (reg_write_adr_w == reg_read_adr1_e))) |-> (forward1_e == 2'h0)
    );

    // Forward1: Encoding is limited to 0/1/2
    fwd1_encoding_valid: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |-> (forward1_e != 2'h3)
    );

    // Forward2: M stage has priority when address matches
    fwd2_from_m_when_match: assert property (
        @(posedge CLK) disable iff (1'b0)
        (reg_write_m && (reg_write_adr_m == reg_read_adr2_e)) |-> (forward2_e == 2'h1)
    );

    // Forward2: W stage selected only if M does not match and W matches
    fwd2_from_w_when_no_m_but_w_match: assert property (
        @(posedge CLK) disable iff (1'b0)
        (! (reg_write_m && (reg_write_adr_m == reg_read_adr2_e)) &&
          (reg_write_w && (reg_write_adr_w == reg_read_adr2_e))) |-> (forward2_e == 2'h2)
    );

    // Forward2: No match in M or W yields no forwarding
    fwd2_none_when_no_matches: assert property (
        @(posedge CLK) disable iff (1'b0)
        (! (reg_write_m && (reg_write_adr_m == reg_read_adr2_e)) &&
         ! (reg_write_w && (reg_write_adr_w == reg_read_adr2_e))) |-> (forward2_e == 2'h0)
    );

    // Forward2: Encoding is limited to 0/1/2
    fwd2_encoding_valid: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |-> (forward2_e != 2'h3)
    );

    // Stalls: stall_f equals stall_d
    stalls_equal: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |-> (stall_f == stall_d)
    );

    // Stalls: stall_d equals flush_e
    stall_equals_flush_e: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |-> (stall_d == flush_e)
    );

    // Flush D: flush_d mirrors PC_source
    flush_d_equals_PC_source: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |-> (flush_d == PC_source)
    );

    // No hazard on D sources -> no stall/flush_e regardless of mem_to_reg_e
    no_hazard_results_no_stall_or_flush_e: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!((reg_write_adr_e == reg_read_adr1_d) || (reg_write_adr_e == reg_read_adr2_d))) |-> 
            (stall_f == 1'b0 && stall_d == 1'b0 && flush_e == 1'b0)
    );

    // Hazard on D sources with mem_to_reg_e -> assert stall_f/stall_d/flush_e
    hazard_and_memtoreg_cause_stall_and_flush_e: assert property (
        @(posedge CLK) disable iff (1'b0)
        (mem_to_reg_e && ((reg_write_adr_e == reg_read_adr1_d) || (reg_write_adr_e == reg_read_adr2_d))) |-> 
            (stall_f == 1'b1 && stall_d == 1'b1 && flush_e == 1'b1)
    );

    // If mem_to_reg_e is 0 then stall_f/stall_d/flush_e must be 0
    memtoreg_low_clears_stall_and_flush_e: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!mem_to_reg_e) |-> (stall_f == 1'b0 && stall_d == 1'b0 && flush_e == 1'b0)
    );
endmodule