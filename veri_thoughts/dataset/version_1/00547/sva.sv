// SVA for counter48: concise, high-quality checks and coverage
module counter48_sva #(
  parameter int DATASIZE = 16
) (
  input  logic                 clk,
  input  logic                 res_n,
  input  logic                 increment,
  input  logic                 load_enable,
  input  logic [DATASIZE-1:0]  load,
  input  logic [DATASIZE-1:0]  value,
  // internal DUT regs (bound by name)
  input  logic                 load_enable_reg,
  input  logic [DATASIZE-1:0]  value_reg
);

  default clocking cb @(posedge clk); endclocking

  // Static/elaboration checks
  initial begin
    assert (DATASIZE >= 1 && DATASIZE <= 48)
      else $error("counter48: DATASIZE=%0d out of range (1..48)", DATASIZE);
    assert ($bits(load)  == DATASIZE);
    assert ($bits(value) == DATASIZE);
  end

  // Connectivity: output mirrors internal register
  a_out_connect: assert property (value == value_reg);

  // Asynchronous reset holds zeros while active
  a_reset_zero:  assert property (@(posedge clk) !res_n |-> (value == '0 && load_enable_reg == 1'b0));

  // Pipeline relation: load_enable_reg is 1-cycle delayed load_enable (outside reset)
  a_le_pipe:     assert property (disable iff (!res_n) $past(res_n) |-> (load_enable_reg == $past(load_enable)));

  // Single-step state transition (covers load priority, increment, and hold)
  a_next_state:  assert property (disable iff (!res_n)
                                  1'b1 |=> value ==
                                    ( $past(load_enable_reg) ? $past(load) :
                                      $past(increment)      ? $past(value) + 1'b1 :
                                                               $past(value) ));

  // No X on output when not in reset
  a_known_value: assert property (res_n |-> !$isunknown(value));

  // Coverage
  c_reset: cover property (@(posedge clk) !res_n ##1 res_n);
  c_load:  cover property (disable iff (!res_n) $past(load_enable_reg) |-> (value == $past(load)));
  c_inc:   cover property (disable iff (!res_n) $past(!load_enable_reg && increment) |-> (value == $past(value)+1'b1));
  c_wrap:  cover property (disable iff (!res_n) (value == {DATASIZE{1'b1}} && !load_enable_reg && increment) |=> (value == '0));

endmodule

// Bind into all counter48 instances; ports connect by name (including internals)
bind counter48 counter48_sva #(.DATASIZE(DATASIZE)) u_counter48_sva (.*);