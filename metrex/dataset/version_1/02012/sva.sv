// SVA bind file for adder, ripple_addsub, and top_module
// Focus: functional correctness, X-prop checks, and concise coverage.
// No clock assumed; using immediate assertions in always_comb.

module adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       cin,
  input  logic [3:0] sum,
  input  logic       cout
);
  logic [4:0] exp;
  always_comb begin
    exp = {1'b0, A} + {1'b0, B} + cin;
    if (!$isunknown({A,B,cin})) begin
      assert ({cout,sum} == exp)
        else $error("adder mismatch: A=%0h B=%0h cin=%0b got {%0b,%0h} exp=%0h",
                    A,B,cin,cout,sum,exp);
      assert (!$isunknown({sum,cout}))
        else $error("adder produced X/Z outputs with known inputs");
    end
    cover (exp[4]);              // carry out
    cover (!exp[4]);             // no carry
    cover (sum == 4'h0);         // zero sum
    cover (&A && &B && cin);     // overflow corner
  end
endmodule

bind adder adder_sva adder_sva_b(.A(A), .B(B), .cin(cin), .sum(sum), .cout(cout));

module ripple_addsub_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       cin,
  input  logic       select,
  input  logic [3:0] sum,
  input  logic       cout
);
  logic [4:0] exp_add, exp_sub;
  always_comb begin
    exp_add = {1'b0, A} + {1'b0, B} + cin;
    exp_sub = ({1'b0, A} + cin) - {1'b0, B};
    if (!$isunknown({A,B,cin,select})) begin
      assert ( select ? ({cout,sum} == exp_sub) : ({cout,sum} == exp_add) )
        else $error("ripple_addsub mismatch: sel=%0b A=%0h B=%0h cin=%0b got {%0b,%0h} exp=%0h",
                    select,A,B,cin,cout,sum, select ? exp_sub : exp_add);
      assert (!$isunknown({sum,cout}))
        else $error("ripple_addsub produced X/Z outputs with known inputs");
    end
    cover (select);              // subtraction path used
    cover (!select);             // addition path used
    cover (select &&  exp_sub[4]); // sub: MSB set (wrap/borrow pattern)
    cover (select && !exp_sub[4]); // sub: MSB clear
    cover (!select && exp_add[4]); // add: carry out
  end
endmodule

bind ripple_addsub ripple_addsub_sva rpa_sva_b(
  .A(A), .B(B), .cin(cin), .select(select), .sum(sum), .cout(cout)
);

module top_module_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       cin,
  input  logic       select,
  input  logic [3:0] sum,
  input  logic       cout
);
  logic [4:0] exp_add, exp_sub, exp_top;
  always_comb begin
    exp_add = {1'b0, A} + {1'b0, B} + cin;
    exp_sub = ({1'b0, A} + cin) - {1'b0, B};
    exp_top = select ? exp_sub : exp_add;

    if (!$isunknown({A,B,cin,select})) begin
      // End-to-end functional spec check
      assert ({cout,sum} == exp_top)
        else $error("top_module spec mismatch: sel=%0b A=%0h B=%0h cin=%0b got {%0b,%0h} exp=%0h",
                    select,A,B,cin,cout,sum,exp_top);
      assert (!$isunknown({sum,cout}))
        else $error("top_module produced X/Z outputs with known inputs");
    end

    // Coverage: both modes, carry/borrow, boundary conditions
    cover (!select && exp_add[4]); // add carry
    cover ( select && exp_sub[4]); // sub MSB set (borrow/wrap)
    cover (sum == 4'h0);
    cover (A==4'h0 && B==4'h0 && cin==1'b0);
    cover (A==4'hF && B==4'hF && cin==1'b1);
  end
endmodule

bind top_module top_module_sva top_sva_b(
  .A(A), .B(B), .cin(cin), .select(select), .sum(sum), .cout(cout)
)