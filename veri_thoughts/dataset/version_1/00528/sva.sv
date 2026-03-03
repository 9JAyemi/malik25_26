// SVA for mux2x4: bindable checker with concise, high-quality properties

module mux2x4_sva (
  input logic [1:0] data0, data1, data2, data3,
  input logic [1:0] selectInput,
  input logic [1:0] out
);

  function automatic logic [1:0] f_mux
    (input logic [1:0] s, d0, d1, d2, d3);
    case (s)
      2'b00: f_mux = d0;
      2'b01: f_mux = d1;
      2'b10: f_mux = d2;
      2'b11: f_mux = d3;
      default: f_mux = 2'b00;
    endcase
  endfunction

  // Golden equivalence vs. the RTL case/default behavior (4-state aware)
  ap_equiv: assert property (@(*)) out === f_mux(selectInput, data0, data1, data2, data3);

  // Functional coverage: all selects and the default path
  cp_s0:      cover property (@(*)) (selectInput == 2'b00 && out === data0);
  cp_s1:      cover property (@(*)) (selectInput == 2'b01 && out === data1);
  cp_s2:      cover property (@(*)) (selectInput == 2'b10 && out === data2);
  cp_s3:      cover property (@(*)) (selectInput == 2'b11 && out === data3);
  cp_default: cover property (@(*)) (!(selectInput inside {2'b00,2'b01,2'b10,2'b11}) && out === 2'b00);

endmodule

bind mux2x4 mux2x4_sva sva_mux2x4 (.*);