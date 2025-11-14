// SVA for ripple_adder and add_sub (concise, high-quality checks + targeted coverage)

// Assertions bound into ripple_adder
module ripple_adder_sva (
  input  logic [15:0] a,
  input  logic [15:0] b,
  input  logic        cin,
  input  logic [15:0] sum,
  input  logic        cout
);
  // Functional correctness
  assert property (@(*) ##0 ({cout,sum} == a + b + cin))
    else $error("ripple_adder mismatch: a=%h b=%h cin=%0d -> {cout,sum}=%h_%h", a,b,cin,cout,sum);

  // Sanity: outputs not X/Z
  assert property (@(*) ##0 !$isunknown({sum,cout}))
    else $error("ripple_adder X/Z on outputs");

  // Targeted coverage
  cover property (@(*) (cin==0));
  cover property (@(*) (cin==1));
  cover property (@(*) (cout==0));
  cover property (@(*) (cout==1));
  cover property (@(*) (a==16'hFFFF && b==16'h0001 && cin==0 && cout==1)); // overflow
  cover property (@(*) (a==16'h0000 && b==16'h0000 && cin==0 && sum==16'h0000 && cout==0));
endmodule

bind ripple_adder ripple_adder_sva u_ripple_adder_sva (.*);


// Assertions bound into add_sub
module add_sub_sva (
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic        sub,
  input  logic [31:0] sum,

  // internal nets from add_sub
  input  logic [15:0] sum_lo,
  input  logic [15:0] sum_hi,
  input  logic        cout
);
  logic [31:0] mask;
  assign mask = {32{sub}};

  // Structural: final XOR matches design intent
  assert property (@(*) ##0 (sum == ({sum_hi,sum_lo} ^ mask)))
    else $error("add_sub structure mismatch: final XOR");

  // Split-add correctness (low 16b and carry)
  assert property (@(*) ##0 ({cout, sum_lo} == (a[15:0] + (b[15:0] ^ {16{sub}}) + sub)))
    else $error("add_sub low-half add mismatch");

  // Split-add correctness (high 16b uses low carry)
  assert property (@(*) ##0 (sum_hi == (a[31:16] + (b[31:16] ^ {16{sub}}) + cout)[15:0]))
    else $error("add_sub high-half add mismatch");

  // 33-bit pre-XOR sum must equal A + (B^mask) + sub
  logic [32:0] exp_pre;
  assign exp_pre = {1'b0,a} + {1'b0,(b ^ mask)} + sub;
  assert property (@(*) ##0 ({1'b0,sum_hi,sum_lo} == exp_pre))
    else $error("add_sub 33b pre-XOR sum mismatch");

  // Golden functionality: sum == (sub ? a - b : a + b)
  assert property (@(*) ##0 (sum == (sub ? (a - b) : (a + b))))
    else $error("add_sub golden mismatch: sub=%0d a=%h b=%h sum=%h exp=%h",
                sub, a, b, sum, (sub ? (a-b):(a+b)));

  // Sanity: output not X/Z
  assert property (@(*) ##0 !$isunknown(sum))
    else $error("add_sub X/Z on sum");

  // Targeted coverage
  cover property (@(*) (sub==0));
  cover property (@(*) (sub==1));
  cover property (@(*) (sub==0 && a==32'hFFFF_FFFF && b==32'h0000_0001)); // add overflow
  cover property (@(*) (sub==1 && a==32'h0000_0000 && b==32'h0000_0001)); // borrow
  cover property (@(*) (sub==1 && a==b));                                  // zero result expected
  cover property (@(*) (cout==1));                                         // carry from low->high
  cover property (@(*) (cout==0));
endmodule

// Bind with internal nets explicitly connected
bind add_sub add_sub_sva u_add_sub_sva (
  .a(a), .b(b), .sub(sub), .sum(sum),
  .sum_lo(sum_lo), .sum_hi(sum_hi), .cout(cout)
);