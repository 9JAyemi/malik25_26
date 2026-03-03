// SVA for mux4_1
module mux4_1_sva (
  input logic       Y,
  input logic       A, B, C, D,
  input logic [1:0] S
);
  default clocking cb @(posedge $global_clock); endclocking

  // Functional correctness for each select value (4-state accurate)
  a_sel00: assert property (S == 2'b00 |-> Y === A);
  a_sel01: assert property (S == 2'b01 |-> Y === B);
  a_sel10: assert property (S == 2'b10 |-> Y === C);
  a_sel11: assert property (S == 2'b11 |-> Y === D);

  // Stability: Y stable if select and selected input are stable (others may toggle)
  a_stable: assert property (
    $stable(S) &&
    ((S==2'b00 && $stable(A)) ||
     (S==2'b01 && $stable(B)) ||
     (S==2'b10 && $stable(C)) ||
     (S==2'b11 && $stable(D)))
    |-> $stable(Y)
  );

  // Knownness: if select is known and selected input is known, Y must be known
  a_known: assert property (
    (S inside {2'b00,2'b01,2'b10,2'b11}) &&
    ((S==2'b00 && !$isunknown(A)) ||
     (S==2'b01 && !$isunknown(B)) ||
     (S==2'b10 && !$isunknown(C)) ||
     (S==2'b11 && !$isunknown(D)))
    |-> !$isunknown(Y)
  );

  // Optional strictness: flag any X/Z on select
  a_no_x_on_S: assert property (!$isunknown(S));

  // Coverage: observe each select path taken
  c_sel00: cover property (S==2'b00 && Y===A);
  c_sel01: cover property (S==2'b01 && Y===B);
  c_sel10: cover property (S==2'b10 && Y===C);
  c_sel11: cover property (S==2'b11 && Y===D);

  // Coverage: hit all four selects over time
  c_all_sel: cover property ((S==2'b00) ##[1:$] (S==2'b01) ##[1:$] (S==2'b10) ##[1:$] (S==2'b11));
endmodule

bind mux4_1 mux4_1_sva sva (.Y(Y), .A(A), .B(B), .C(C), .D(D), .S(S));