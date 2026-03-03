// SVA for select_logic – concise, high-quality checks and coverage
// Bind this file to the DUT: bind select_logic select_logic_sva u_sva (.*);

module select_logic_sva(
  input i1, i2, i3, i4, i5, i6, i7, i8,
  input s1, s2, s3,
  input a1
);

  wire [2:0] sel = {s1,s2,s3};

  // Decode
  wire d0 = (sel == 3'b000);
  wire d1 = (sel == 3'b001);
  wire d2 = (sel == 3'b010);
  wire d3 = (sel == 3'b011);
  wire d4 = (sel == 3'b100);
  wire d5 = (sel == 3'b101);
  wire d6 = (sel == 3'b110);
  wire d7 = (sel == 3'b111);

  // Basic sanity/X checks
  assert property (@(*)) !$isunknown(sel)
    else $error("select_logic: s1/s2/s3 contain X/Z");

  // Exactly one decode active
  assert property (@(*)) $onehot({d7,d6,d5,d4,d3,d2,d1,d0})
    else $error("select_logic: decode not one-hot");

  // Functional correctness: output equals selected input
  assert property (@(*)) d0 |-> (a1 == i1);
  assert property (@(*)) d1 |-> (a1 == i2);
  assert property (@(*)) d2 |-> (a1 == i3);
  assert property (@(*)) d3 |-> (a1 == i4);
  assert property (@(*)) d4 |-> (a1 == i5);
  assert property (@(*)) d5 |-> (a1 == i6);
  assert property (@(*)) d6 |-> (a1 == i7);
  assert property (@(*)) d7 |-> (a1 == i8);

  // Optional consolidated equivalence (guards regressions succinctly)
  assert property (@(*))
    a1 == ((d0&i1)|(d1&i2)|(d2&i3)|(d3&i4)|(d4&i5)|(d5&i6)|(d6&i7)|(d7&i8));

  // Functional coverage: hit all selects, and both a1=0/1 under each select
  cover property (@(*)) d0;  cover property (@(*)) d0 &&  a1;  cover property (@(*)) d0 && !a1;
  cover property (@(*)) d1;  cover property (@(*)) d1 &&  a1;  cover property (@(*)) d1 && !a1;
  cover property (@(*)) d2;  cover property (@(*)) d2 &&  a1;  cover property (@(*)) d2 && !a1;
  cover property (@(*)) d3;  cover property (@(*)) d3 &&  a1;  cover property (@(*)) d3 && !a1;
  cover property (@(*)) d4;  cover property (@(*)) d4 &&  a1;  cover property (@(*)) d4 && !a1;
  cover property (@(*)) d5;  cover property (@(*)) d5 &&  a1;  cover property (@(*)) d5 && !a1;
  cover property (@(*)) d6;  cover property (@(*)) d6 &&  a1;  cover property (@(*)) d6 && !a1;
  cover property (@(*)) d7;  cover property (@(*)) d7 &&  a1;  cover property (@(*)) d7 && !a1;

endmodule

// Bind to the DUT
bind select_logic select_logic_sva u_sva (.*);