// SVA for EHR_6: checks reset, read-chain correctness, next-state update, priority, and provides concise coverage

module EHR_6_sva #(
  parameter int DATA_SZ   = 1,
  parameter int RESET_VAL = 0
)(
  input logic                    CLK,
  input logic                    RST_N,
  input logic [DATA_SZ-1:0]      read_0, read_1, read_2, read_3, read_4, read_5,
  input logic [DATA_SZ-1:0]      write_0, write_1, write_2, write_3, write_4, write_5,
  input logic                    EN_write_0, EN_write_1, EN_write_2, EN_write_3, EN_write_4, EN_write_5,
  input logic [DATA_SZ-1:0]      r
);

  default clocking cb @(posedge CLK); endclocking

  // Expected combinational chain and next-state
  logic [DATA_SZ-1:0] exp_r0, exp_r1, exp_r2, exp_r3, exp_r4, exp_r5, exp_next;
  always_comb begin
    exp_r0  = r;
    exp_r1  = EN_write_0 ? write_0 : exp_r0;
    exp_r2  = EN_write_1 ? write_1 : exp_r1;
    exp_r3  = EN_write_2 ? write_2 : exp_r2;
    exp_r4  = EN_write_3 ? write_3 : exp_r3;
    exp_r5  = EN_write_4 ? write_4 : exp_r4;
    exp_next= EN_write_5 ? write_5 : exp_r5;
  end

  // Helper predicates
  function automatic logic none_higher_en(input int j);
    case (j)
      0: none_higher_en = !(EN_write_1||EN_write_2||EN_write_3||EN_write_4||EN_write_5);
      1: none_higher_en = !(EN_write_2||EN_write_3||EN_write_4||EN_write_5);
      2: none_higher_en = !(EN_write_3||EN_write_4||EN_write_5);
      3: none_higher_en = !(EN_write_4||EN_write_5);
      4: none_higher_en = !(EN_write_5);
      5: none_higher_en = 1'b1;
      default: none_higher_en = 1'b0;
    endcase
  endfunction

  function automatic logic no_en_any();
    return !(EN_write_0||EN_write_1||EN_write_2||EN_write_3||EN_write_4||EN_write_5);
  endfunction

  function automatic logic only_j_high(input int j);
    case (j)
      0: only_j_high = EN_write_0 && !(EN_write_1||EN_write_2||EN_write_3||EN_write_4||EN_write_5);
      1: only_j_high = EN_write_1 && !(EN_write_0||EN_write_2||EN_write_3||EN_write_4||EN_write_5);
      2: only_j_high = EN_write_2 && !(EN_write_0||EN_write_1||EN_write_3||EN_write_4||EN_write_5);
      3: only_j_high = EN_write_3 && !(EN_write_0||EN_write_1||EN_write_2||EN_write_4||EN_write_5);
      4: only_j_high = EN_write_4 && !(EN_write_0||EN_write_1||EN_write_2||EN_write_3||EN_write_5);
      5: only_j_high = EN_write_5 && !(EN_write_0||EN_write_1||EN_write_2||EN_write_3||EN_write_4);
      default: only_j_high = 1'b0;
    endcase
  endfunction

  // Reset behavior (synchronous)
  a_reset_hold:         assert property (!RST_N |-> r == RESET_VAL);
  a_reset_release_step: assert property (!$past(RST_N) && RST_N |-> r == RESET_VAL);

  // Read-chain correctness (combinational path)
  a_read0: assert property (read_0 == exp_r0);
  a_read1: assert property (read_1 == exp_r1);
  a_read2: assert property (read_2 == exp_r2);
  a_read3: assert property (read_3 == exp_r3);
  a_read4: assert property (read_4 == exp_r4);
  a_read5: assert property (read_5 == exp_r5);

  // Next-state update equals mux-chain result when enabled
  a_next_state: assert property ($past(RST_N) && RST_N |-> r == $past(exp_next));

  // Priority correctness: highest-index enabled port wins
  genvar j;
  generate
    for (j=0; j<6; j++) begin : gen_pri
      a_pri: assert property ($past(RST_N) && $past(EN_write_``j) && $past(none_higher_en(j)) |-> r == $past(write_``j));
    end
  endgenerate

  // Hold when no writes
  a_hold: assert property ($past(RST_N) && $past(no_en_any()) |-> r == $past(r));

  // Coverage
  c_reset:     cover property (!RST_N ##1 RST_N);
  c_hold:      cover property (RST_N && no_en_any() ##1 r == $past(r));
  generate
    for (j=0; j<6; j++) begin : gen_cov_single
      c_single_sel: cover property (RST_N && only_j_high(j) ##1 r == $past(write_``j));
    end
  endgenerate
  c_override_example: cover property (RST_N && EN_write_0 && EN_write_5 && !(EN_write_1||EN_write_2||EN_write_3||EN_write_4) ##1 r == $past(write_5));
  c_all_high:         cover property (RST_N && (EN_write_0&&EN_write_1&&EN_write_2&&EN_write_3&&EN_write_4&&EN_write_5) ##1 r == $past(write_5));

endmodule

// Bind into the DUT
bind EHR_6 EHR_6_sva #(.DATA_SZ(DATA_SZ), .RESET_VAL(RESET_VAL)) EHR_6_sva_i (.*);