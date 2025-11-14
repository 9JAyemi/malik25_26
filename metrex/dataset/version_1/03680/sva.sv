// SVA for top_module, mux2to1, and adder
// Concise, high-quality checks + targeted coverage. Bind into DUT.

// 1) Submodule checks

module mux2to1_sva(input [3:0] a, b, input sel, input [3:0] out);
  // Functional correctness when inputs are known
  assert property (@(*)
    !$isunknown({a,b,sel}) |-> (out == (sel ? b : a))
  );

  // Coverage: both arms taken
  cover property (@(*) !$isunknown(sel) && (sel == 1'b0));
  cover property (@(*) !$isunknown(sel) && (sel == 1'b1));
endmodule

bind mux2to1 mux2to1_sva i_mux2to1_sva(.a(a), .b(b), .sel(sel), .out(out));

module adder_sva(input [3:0] a, b, input [7:0] sum);
  // Exact zero-extended addition
  assert property (@(*)
    !$isunknown({a,b}) |-> (sum == ({4'b0, a} + {4'b0, b}))
  );

  // Coverage: carry into upper nibble vs none
  cover property (@(*) !$isunknown({a,b}) &&
                  (({4'b0,a}+{4'b0,b})[7:4] == 0));
  cover property (@(*) !$isunknown({a,b}) &&
                  (({4'b0,a}+{4'b0,b})[7:4] != 0));
endmodule

bind adder adder_sva i_adder_sva(.a(a), .b(b), .sum(sum));


// 2) Top-level end-to-end checks (port-level, no internal refs)

module top_module_sva(input [3:0] a1, a2, b1, b2,
                      input sel1, sel2, select,
                      input [3:0] out);
  let mux1_exp = sel1 ? b1 : a1;
  let mux2_exp = sel2 ? b2 : a2;
  let active_exp = select ? mux2_exp : mux1_exp;
  let sum8_exp = {4'b0, active_exp} + {4'b0, mux2_exp};

  // End-to-end functional equivalence on visible outputs
  assert property (@(*)
    !$isunknown({a1,a2,b1,b2,sel1,sel2,select}) |-> (out == sum8_exp[3:0])
  );

  // Control-space coverage (all 8 combinations)
  cover property (@(*) !$isunknown({sel1,sel2,select}) && {sel1,sel2,select} == 3'b000);
  cover property (@(*) !$isunknown({sel1,sel2,select}) && {sel1,sel2,select} == 3'b001);
  cover property (@(*) !$isunknown({sel1,sel2,select}) && {sel1,sel2,select} == 3'b010);
  cover property (@(*) !$isunknown({sel1,sel2,select}) && {sel1,sel2,select} == 3'b011);
  cover property (@(*) !$isunknown({sel1,sel2,select}) && {sel1,sel2,select} == 3'b100);
  cover property (@(*) !$isunknown({sel1,sel2,select}) && {sel1,sel2,select} == 3'b101);
  cover property (@(*) !$isunknown({sel1,sel2,select}) && {sel1,sel2,select} == 3'b110);
  cover property (@(*) !$isunknown({sel1,sel2,select}) && {sel1,sel2,select} == 3'b111);

  // Carry/no-carry coverage at the top level
  cover property (@(*) !$isunknown({a1,a2,b1,b2,sel1,sel2,select}) &&
                  (sum8_exp[7:4] == 0));
  cover property (@(*) !$isunknown({a1,a2,b1,b2,sel1,sel2,select}) &&
                  (sum8_exp[7:4] != 0));
endmodule

bind top_module top_module_sva i_top_module_sva(
  .a1(a1), .a2(a2), .b1(b1), .b2(b2),
  .sel1(sel1), .sel2(sel2), .select(select),
  .out(out)
);


// 3) Optional internal consistency checks inside top_module

module top_module_int_sva(input [3:0] mux1_out, mux2_out, active_mux_out,
                          input [7:0] sum, input [3:0] out,
                          input sel1, sel2, select);
  // Internal select logic consistent
  assert property (@(*)
    !$isunknown({select,mux1_out,mux2_out}) |->
      (active_mux_out == (select ? mux2_out : mux1_out))
  );

  // Adder wiring and output slice consistent
  assert property (@(*)
    !$isunknown({active_mux_out, mux2_out}) |->
      (sum == ({4'b0,active_mux_out} + {4'b0,mux2_out}))
  );
  assert property (@(*)
    !$isunknown(sum) |-> (out == sum[3:0])
  );

  // Coverage: select path toggles
  cover property (@(*) !$isunknown(select) && (select==1'b0));
  cover property (@(*) !$isunknown(select) && (select==1'b1));
endmodule

bind top_module top_module_int_sva i_top_module_int_sva(
  .mux1_out(mux1_out),
  .mux2_out(mux2_out),
  .active_mux_out(active_mux_out),
  .sum(sum),
  .out(out),
  .sel1(sel1), .sel2(sel2), .select(select)
);