// SVA for my_alu (bindable checker). Provide a sampling clock.
// Bind example (from TB): bind my_alu my_alu_sva #(.N(N)) u_chk (.clk(tb_clk), .a(a), .b(b), .op(op), .result(result), .carry(carry));

module my_alu_sva #(parameter int N = 8)
(
  input  logic                      clk,
  input  logic signed [N-1:0]       a,
  input  logic signed [N-1:0]       b,
  input  logic        [3:0]         op,
  input  logic signed [N-1:0]       result,
  input  logic                      carry
);

  default clocking cb @(posedge clk); endclocking

  // Helpers
  let ONE        = {{N-1{1'b0}},1'b1};
  let ADD_RES    = $signed(a) + $signed(b);
  let SUB_RES    = $signed(a) - $signed(b);
  let SHL_RES    = (a << b);
  let SHR_RES    = (a >> b); // a is signed: arithmetic right shift as in DUT
  let ASHR_EXT   = $signed({a[N-1], a}) >>> b; // N+1 wide
  let ASHR_RES   = ASHR_EXT[N-1:0];

  // Basic sanity: no X on outputs when inputs are known; pure combinational behavior
  assert property (!$isunknown({a,b,op}) |-> !$isunknown({result,carry}));
  assert property ($stable({a,b,op}) |-> $stable({result,carry}));

  // Full functional checks per opcode (zero-latency, same-cycle)
  // 0000: a + b, carry = signed overflow per DUT formula
  assert property (op==4'b0000 |-> (result==ADD_RES) &&
                                  (carry == ((result[N-1]==a[N-1]) && (result[N-1]==b[N-1]))));

  // 0001: a - b, carry = signed overflow per DUT formula
  assert property (op==4'b0001 |-> (result==SUB_RES) &&
                                  (carry == ((result[N-1]==a[N-1]) && (result[N-1]!=b[N-1]))));

  // 0010: a & b
  assert property (op==4'b0010 |-> (result==(a & b)) && (carry==1'b0));

  // 0011: a | b
  assert property (op==4'b0011 |-> (result==(a | b)) && (carry==1'b0));

  // 0100: a ^ b
  assert property (op==4'b0100 |-> (result==(a ^ b)) && (carry==1'b0));

  // 0101: ~a
  assert property (op==4'b0101 |-> (result==~a) && (carry==1'b0));

  // 0110: ~b
  assert property (op==4'b0110 |-> (result==~b) && (carry==1'b0));

  // 0111: 0
  assert property (op==4'b0111 |-> (result=='0) && (carry==1'b0));

  // 1000: a << b, carry = MSB(result)
  assert property (op==4'b1000 |-> (result==SHL_RES) && (carry==result[N-1]));

  // 1001: a >> b (arith), carry = LSB(result)
  assert property (op==4'b1001 |-> (result==SHR_RES) && (carry==result[0]));

  // 1010: a >>> b via sign-extended path in DUT, carry = LSB(result)
  assert property (op==4'b1010 |-> (result==ASHR_RES) && (carry==result[0]));

  // 1011: a == b  (result 0/1), carry=0
  assert property (op==4'b1011 |-> (result inside {'0, ONE}) &&
                                  (result== (a==b ? ONE : '0)) &&
                                  (carry==1'b0));

  // 1100: a != b  (result 0/1), carry=0
  assert property (op==4'b1100 |-> (result inside {'0, ONE}) &&
                                  (result== (a!=b ? ONE : '0)) &&
                                  (carry==1'b0));

  // 1101: a > b   (signed, result 0/1), carry=0
  assert property (op==4'b1101 |-> (result inside {'0, ONE}) &&
                                  (result== (a>b ? ONE : '0)) &&
                                  (carry==1'b0));

  // 1110: a >= b  (signed, result 0/1), carry=0
  assert property (op==4'b1110 |-> (result inside {'0, ONE}) &&
                                  (result== (a>=b ? ONE : '0)) &&
                                  (carry==1'b0));

  // 1111: a < b   (signed, result 0/1), carry=0
  assert property (op==4'b1111 |-> (result inside {'0, ONE}) &&
                                  (result== (a<b ? ONE : '0)) &&
                                  (carry==1'b0));

  // Grouped invariant: ops that should never set carry
  assert property ((op inside {4'b0010,4'b0011,4'b0100,4'b0101,4'b0110,4'b0111,4'b1011,4'b1100,4'b1101,4'b1110,4'b1111}) |-> carry==1'b0);

  // Minimal functional coverage
  cover property (op==4'b0000 && carry);      // add overflow asserted
  cover property (op==4'b0000 && !carry);     // add overflow deasserted
  cover property (op==4'b0001 && carry);      // sub overflow asserted
  cover property (op==4'b0001 && !carry);     // sub overflow deasserted
  cover property (op==4'b1000 && result[N-1]); // shl carry=1
  cover property (op==4'b1001 && result[0]);   // shr carry=1
  cover property (op==4'b1010 && result[0]);   // ashr carry=1
  cover property (op inside {4'b1000,4'b1001,4'b1010} && $unsigned(b)==0);     // shift by 0
  cover property (op inside {4'b1000,4'b1001,4'b1010} && $unsigned(b)>=N);     // large shift
  cover property (op==4'b0111 && result=='0);
  cover property (op==4'b1011 && result==ONE); // equality true
  cover property (op==4'b1011 && result=='0);  // equality false
  cover property (op==4'b1101 && result==ONE); // >
  cover property (op==4'b1101 && result=='0);
  cover property (op==4'b1110 && result==ONE); // >=
  cover property (op==4'b1110 && result=='0);
  cover property (op==4'b1111 && result==ONE); // <
  cover property (op==4'b1111 && result=='0);

endmodule