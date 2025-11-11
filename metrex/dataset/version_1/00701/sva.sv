// SVA for mux21, demux, mux41
// Bind these after compiling the DUT

// 2:1 MUX assertions
module mux21_sva (input A, B, S, Y);
  // Functional correctness (4-state)
  a_func: assert property (@(*)
    Y === ((~S & A) | (S & B))
  );

  // Selection coverage
  c_sel0: cover property (@(*) !S && (Y === A));
  c_sel1: cover property (@(*)  S && (Y === B));
  c_ps:   cover property (@(posedge S) 1);
  c_ns:   cover property (@(negedge S) 1);
endmodule
bind mux21 mux21_sva mux21_sva_i (.A(A), .B(B), .S(S), .Y(Y));

// "demux" is actually a 4:1 MUX built from 2:1 MUXes
module demux_sva (input in0, in1, in2, in3, d0, d1, out);
  // End-to-end functional correctness (4-state)
  a_func: assert property (@(*)
    out === (d1 ? (d0 ? in3 : in2) : (d0 ? in1 : in0))
  );

  // Selection coverage
  c_00: cover property (@(*) ({d1,d0}==2'b00) && (out===in0));
  c_01: cover property (@(*) ({d1,d0}==2'b01) && (out===in1));
  c_10: cover property (@(*) ({d1,d0}==2'b10) && (out===in2));
  c_11: cover property (@(*) ({d1,d0}==2'b11) && (out===in3));
  c_pd0: cover property (@(posedge d0) 1);
  c_nd0: cover property (@(negedge d0) 1);
  c_pd1: cover property (@(posedge d1) 1);
  c_nd1: cover property (@(negedge d1) 1);

  // Unselected inputs do not affect output
  a_no_side_effects: assert property (@(*)
    $stable({d1,d0}) &&
    (((!d1 && !d0) && $stable(in0) && $changed({in1,in2,in3})) ||
     ((!d1 &&  d0) && $stable(in1) && $changed({in0,in2,in3})) ||
     (( d1 && !d0) && $stable(in2) && $changed({in0,in1,in3})) ||
     (( d1 &&  d0) && $stable(in3) && $changed({in0,in1,in2})))
    |-> $stable(out)
  );
endmodule
bind demux demux_sva demux_sva_i (.in0(in0), .in1(in1), .in2(in2), .in3(in3), .d0(d0), .d1(d1), .out(out));

// 4:1 MUX assertions (note: B* are unused by DUT; assert independence)
module mux41_sva (input A0,A1,A2,A3, B0,B1,B2,B3, S0,S1, Y);
  // Functional correctness (4-state)
  a_func: assert property (@(*)
    Y === (S1 ? (S0 ? A3 : A2) : (S0 ? A1 : A0))
  );

  // Selection coverage
  c_00: cover property (@(*) ({S1,S0}==2'b00) && (Y===A0));
  c_01: cover property (@(*) ({S1,S0}==2'b01) && (Y===A1));
  c_10: cover property (@(*) ({S1,S0}==2'b10) && (Y===A2));
  c_11: cover property (@(*) ({S1,S0}==2'b11) && (Y===A3));
  c_ps0: cover property (@(posedge S0) 1);
  c_ns0: cover property (@(negedge S0) 1);
  c_ps1: cover property (@(posedge S1) 1);
  c_ns1: cover property (@(negedge S1) 1);

  // Y is independent of B* when A*,S* are stable
  a_B_indep: assert property (@(*)
    $changed({B0,B1,B2,B3}) && $stable({A0,A1,A2,A3,S0,S1}) |-> $stable(Y)
  );
endmodule
bind mux41 mux41_sva mux41_sva_i (
  .A0(A0), .A1(A1), .A2(A2), .A3(A3),
  .B0(B0), .B1(B1), .B2(B2), .B3(B3),
  .S0(S0), .S1(S1), .Y(Y)
);