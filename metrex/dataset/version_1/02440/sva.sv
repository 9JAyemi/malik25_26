// SVA for anteconmutador
// Bind to DUT to access internal signals digitT and i
module anteconmutador_sva (
  input logic        clk,
  input logic [7:0]  count,
  input logic        calculate,
  input logic [3:0]  centenas,
  input logic [3:0]  decenas,
  input logic [3:0]  unidades,
  input logic        C,
  input logic        De,
  input logic        U,
  input logic [7:0]  digitT,
  input logic        i
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior when calculate==0 (same-cycle)
  assert property (!calculate |-> (digitT==8'd0 && C==0 && De==0 && U==0 && i==1 &&
                                   centenas==4'd0 && decenas==4'd0 && unidades==4'd0));

  // On rising calculate, capture count into digitT and drop i
  assert property ($rose(calculate) |-> (i==0 && digitT==count));

  // While calculate stays high, i must remain 0
  assert property (calculate && $past(calculate) |-> i==0);

  // Hundreds step
  assert property ($past(calculate) && calculate && $past(i)==0 && $past(digitT)>8'd99 |->
                   digitT==$past(digitT)-8'd100 &&
                   centenas==$past(centenas)+1 &&
                   decenas==$past(decenas) &&
                   unidades==$past(unidades) &&
                   C==$past(C) && De==$past(De) && U==$past(U));

  // Tens step
  assert property ($past(calculate) && calculate && $past(i)==0 &&
                   $past(digitT)<=8'd99 && $past(digitT)>8'd9 |->
                   digitT==$past(digitT)-8'd10 &&
                   decenas==$past(decenas)+1 &&
                   centenas==$past(centenas) &&
                   unidades==$past(unidades) &&
                   C==$past(C) && De==$past(De) && U==$past(U));

  // First units/final step
  assert property ($past(calculate) && calculate && $past(i)==0 && $past(digitT)<=8'd9 |->
                   unidades==$past(digitT[3:0]) &&
                   centenas==$past(centenas) && decenas==$past(decenas) &&
                   digitT==$past(digitT) &&
                   C==(centenas>=1) && De==(decenas>=1) && U==(unidades>=1));

  // Finished invariant (holds every cycle once digitT<=9)
  assert property (calculate && i==0 && digitT<=8'd9 |->
                   (unidades==digitT[3:0]) &&
                   C==(centenas>=1) && De==(decenas>=1) && U==(unidades>=1));

  // Monotonicity and non-decreasing decimal counters during conversion
  assert property ($past(calculate) && calculate && $past(i)==0 && $past(digitT)>8'd9 |->
                   digitT <= $past(digitT));
  assert property ($past(calculate) && calculate && $past(i)==0 |->
                   (centenas>=$past(centenas)) && (decenas>=$past(decenas)));

  // End-to-end correctness: within 12 cycles after start, digits/flags match the captured count
  property p_correct_decomp;
    int cnt;
    ($rose(calculate) ##0 (cnt = count, 1)) |-> ##[1:12]
      (calculate && i==0 && digitT<=8'd9 &&
       (100*centenas + 10*decenas + unidades) == cnt &&
       C==(centenas>=1) && De==(decenas>=1) && U==(unidades>=1));
  endproperty
  assert property (p_correct_decomp);

  // Coverage: representative values and paths
  cover property ($rose(calculate) && count==8'd255 ##[1:12]
                  (calculate && digitT<=8'd9 && centenas==4'd2 && decenas==4'd5 && unidades==4'd5 && C && De && U));
  cover property ($rose(calculate) && count==8'd200 ##[1:12]
                  (calculate && digitT<=8'd9 && centenas==4'd2 && decenas==4'd0 && unidades==4'd0 && C && !De && !U));
  cover property ($rose(calculate) && count==8'd73 ##[1:12]
                  (calculate && digitT<=8'd9 && centenas==4'd0 && decenas==4'd7 && unidades==4'd3 && !C && De && U));
  cover property ($rose(calculate) && count==8'd0 ##[1:5]
                  (calculate && digitT<=8'd9 && centenas==0 && decenas==0 && unidades==0 && !C && !De && !U));
endmodule

bind anteconmutador anteconmutador_sva sva_i (
  .clk(clk),
  .count(count),
  .calculate(calculate),
  .centenas(centenas),
  .decenas(decenas),
  .unidades(unidades),
  .C(C),
  .De(De),
  .U(U),
  .digitT(digitT),
  .i(i)
);