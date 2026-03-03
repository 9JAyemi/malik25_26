// SVA checker for adder
module adder_sva
(
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic [3:0] sum,
  input  logic       carry,
  input  logic [3:0] sum_buf,
  input  logic       carry_buf
);

  // Core functional correctness and sanity
  always_comb begin
    assert ({carry, sum} === a + b)
      else $error("adder mismatch: a=%0d b=%0d -> sum=%0d carry=%0b", a,b,sum,carry);

    if (!$isunknown({a,b})) begin
      assert (!$isunknown({sum,carry}))
        else $error("adder outputs X/Z with known inputs: a=%0h b=%0h sum=%0h carry=%0b", a,b,sum,carry);
    end

    assert (sum_buf === sum)
      else $error("sum_buf != sum: %0h != %0h", sum_buf, sum);

    assert (carry_buf === carry)
      else $error("carry_buf != carry: %0b != %0b", carry_buf, carry);

    // 4-bit + 4-bit cannot produce total 31 (carry==1 and sum==15)
    assert (!(carry && (sum == 4'hF)))
      else $error("illegal total 31 detected: a=%0d b=%0d", a, b);
  end

  // Functional coverage (full operand cross + result distribution)
  event cg_ev;
  always @(a or b or sum or carry) -> cg_ev;

  covergroup cg @(cg_ev);
    option.per_instance = 1;

    cp_a: coverpoint a iff (!$isunknown(a)) { bins all[] = {[0:15]}; }
    cp_b: coverpoint b iff (!$isunknown(b)) { bins all[] = {[0:15]}; }
    x_ab: cross cp_a, cp_b;

    cp_total: coverpoint {carry, sum} iff (!$isunknown({a,b,sum,carry})) {
      bins all[]      = {[0:30]};     // all legal totals
      bins ovf[]      = {[16:30]};    // carry == 1
      bins no_ovf[]   = {[0:15]};     // carry == 0
      bins zero       = {0};          // 0+0
      bins fifteen    = {15};         // e.g., 8+7
      bins max_total  = {30};         // 15+15
      illegal_bins gt30 = {[31:$]};
    }

    // Key operand corners
    c_zero_zero:      coverpoint {a,b} iff (!$isunknown({a,b})) { bins both_zero      = {8'h00}; }
    c_max_plus_zero:  coverpoint {a,b} iff (!$isunknown({a,b})) { bins a_max_b_zero   = {8'hF0};
                                                                  bins a_zero_b_max   = {8'h0F}; }
    c_max_plus_one:   coverpoint {a,b} iff (!$isunknown({a,b})) { bins max_plus_one[] = {8'hF1, 8'h1F}; }
  endgroup

  cg cg_i = new();

endmodule

// Bind to DUT (auto-connects internal sum_buf/carry_buf as well)
bind adder adder_sva u_adder_sva (.*)