// SVA for module 'inicial' (concise, quality-focused)
// Bind this file in your simulation: bind inicial inicial_sva i_inicial_sva();

module inicial_sva (inicial dut);

  default clocking cb @(posedge dut.clock); endclocking

  // State aliases
  localparam [2:0] A = dut.A, B = dut.B, C = dut.C, D = dut.D, E = dut.E;

  // Expected next-state function (mirrors DUT priority/behavior)
  function automatic [2:0] exp_next(input [2:0] s, input [3:0] t);
    case (s)
      A: exp_next = (t==4'b1100)                        ? B :
                    (t==4'b1101 || t==4'b1111)          ? C :
                    (t==4'b1110)                        ? D :
                    (t==4'b1010)                        ? E : s;
      B: exp_next = (t==4'b0000 || t==4'b1000)          ? A :
                    (t==4'b1101)                        ? C :
                    (t==4'b1110 || t==4'b1111)          ? D :
                    (t==4'b1010 || t==4'b1011)          ? E : s;
      C: exp_next = (t==4'b0100 || t==4'b1100)          ? B :
                    (t==4'b0000 || t==4'b1000)          ? A :
                    (t==4'b0110 || t==4'b1110)          ? D :
                    (t==4'b1010)                        ? E : s;
      D: exp_next = (t==4'b0111 || t==4'b1111)          ? C :
                    (t==4'b1100)                        ? B :
                    (t==4'b1010)                        ? E :
                    (t==4'b0000 || t==4'b1000)          ? A : s;
      E: exp_next = (t==4'b0000 || t==4'b1000)          ? A :
                    (t==4'b0110 || t==4'b1110)          ? D :
                    (t==4'b1100)                        ? B :
                    (t==4'b1101)                        ? C : s;
      default: exp_next = A;
    endcase
  endfunction

  // Convenience
  wire [3:0] t = {dut.giro, dut.entrada, dut.saida, dut.metais};

  // 1) Initialization/state legality
  initial assert (dut.estado == A);
  assert property (dut.estado inside {A,B,C,D,E});

  // 2) Input capture into tmp (should mirror inputs each clk)
  assert property (dut.tmp == t);

  // 3) Next-state function check (one-cycle lookahead)
  assert property (dut.estado == exp_next($past(dut.estado), $past(t)));

  // 4) Moore outputs must match previous state (due to update ordering)
  assert property ($past(dut.estado)==A |-> (dut.ledVerde==2'b00 && dut.ledVermelho==2'b00 && dut.display==7'b1111001));
  assert property ($past(dut.estado)==B |-> (dut.ledVerde==2'b01 && dut.ledVermelho==2'b00 && dut.display==7'b0100100));
  assert property ($past(dut.estado)==C |-> (dut.ledVerde==2'b00 && dut.ledVermelho==2'b01 && dut.display==7'b0110000));
  assert property ($past(dut.estado)==D |-> (dut.ledVerde==2'b10 && dut.ledVermelho==2'b10 && dut.display==7'b0011001));
  assert property ($past(dut.estado)==E |-> (dut.ledVerde==2'b00 && dut.ledVermelho==2'b00 && dut.display==7'b0010010));

  // 5) Transition coverage (all arcs via explicit input patterns)
  // From A
  cover property ($past(dut.estado)==A && $past(t)==4'b1100 |=> dut.estado==B);
  cover property ($past(dut.estado)==A && $past(t)==4'b1101 |=> dut.estado==C);
  cover property ($past(dut.estado)==A && $past(t)==4'b1111 |=> dut.estado==C);
  cover property ($past(dut.estado)==A && $past(t)==4'b1110 |=> dut.estado==D);
  cover property ($past(dut.estado)==A && $past(t)==4'b1010 |=> dut.estado==E);

  // From B
  cover property ($past(dut.estado)==B && $past(t)==4'b0000 |=> dut.estado==A);
  cover property ($past(dut.estado)==B && $past(t)==4'b1000 |=> dut.estado==A);
  cover property ($past(dut.estado)==B && $past(t)==4'b1101 |=> dut.estado==C);
  cover property ($past(dut.estado)==B && $past(t)==4'b1110 |=> dut.estado==D);
  cover property ($past(dut.estado)==B && $past(t)==4'b1111 |=> dut.estado==D);
  cover property ($past(dut.estado)==B && $past(t)==4'b1010 |=> dut.estado==E);
  cover property ($past(dut.estado)==B && $past(t)==4'b1011 |=> dut.estado==E);

  // From C
  cover property ($past(dut.estado)==C && $past(t)==4'b0100 |=> dut.estado==B);
  cover property ($past(dut.estado)==C && $past(t)==4'b1100 |=> dut.estado==B);
  cover property ($past(dut.estado)==C && $past(t)==4'b0000 |=> dut.estado==A);
  cover property ($past(dut.estado)==C && $past(t)==4'b1000 |=> dut.estado==A);
  cover property ($past(dut.estado)==C && $past(t)==4'b0110 |=> dut.estado==D);
  cover property ($past(dut.estado)==C && $past(t)==4'b1110 |=> dut.estado==D);
  cover property ($past(dut.estado)==C && $past(t)==4'b1010 |=> dut.estado==E);

  // From D
  cover property ($past(dut.estado)==D && $past(t)==4'b0111 |=> dut.estado==C);
  cover property ($past(dut.estado)==D && $past(t)==4'b1111 |=> dut.estado==C);
  cover property ($past(dut.estado)==D && $past(t)==4'b1100 |=> dut.estado==B);
  cover property ($past(dut.estado)==D && $past(t)==4'b1010 |=> dut.estado==E);
  cover property ($past(dut.estado)==D && $past(t)==4'b0000 |=> dut.estado==A);
  cover property ($past(dut.estado)==D && $past(t)==4'b1000 |=> dut.estado==A);

  // From E
  cover property ($past(dut.estado)==E && $past(t)==4'b0000 |=> dut.estado==A);
  cover property ($past(dut.estado)==E && $past(t)==4'b1000 |=> dut.estado==A);
  cover property ($past(dut.estado)==E && $past(t)==4'b0110 |=> dut.estado==D);
  cover property ($past(dut.estado)==E && $past(t)==4'b1110 |=> dut.estado==D);
  cover property ($past(dut.estado)==E && $past(t)==4'b1100 |=> dut.estado==B);
  cover property ($past(dut.estado)==E && $past(t)==4'b1101 |=> dut.estado==C);

  // 6) State and output coverage
  cover property (dut.estado==A);
  cover property (dut.estado==B);
  cover property (dut.estado==C);
  cover property (dut.estado==D);
  cover property (dut.estado==E);

  cover property (dut.display==7'b1111001);
  cover property (dut.display==7'b0100100);
  cover property (dut.display==7'b0110000);
  cover property (dut.display==7'b0011001);
  cover property (dut.display==7'b0010010);

endmodule

bind inicial inicial_sva i_inicial_sva(.dut());