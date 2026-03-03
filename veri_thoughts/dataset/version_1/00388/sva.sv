// SVA for data_converter (bind-ready, clockless/combinational)

module data_converter_sva (
  input  logic [3:0] data_in,
  input  logic [1:0] data_out
);

  function automatic logic [1:0] enc (input logic [3:0] di);
    enc = (di <= 4)  ? 2'b00 :
          (di <= 8)  ? 2'b01 :
          (di <= 12) ? 2'b10 : 2'b11;
  endfunction

  // Correct mapping for known inputs (##0 avoids delta races)
  property p_map_correct;
    @(data_in or data_out)
      (!$isunknown(data_in)) |-> ##0 (data_out == enc(data_in));
  endproperty
  assert property (p_map_correct)
    else $error("data_out mismatch: in=%0d out=%b exp=%b", data_in, data_out, enc(data_in));

  // For known input, output must be known (no X/Z)
  property p_known_out_when_known_in;
    @(data_in or data_out)
      (!$isunknown(data_in)) |-> ##0 (!$isunknown(data_out));
  endproperty
  assert property (p_known_out_when_known_in)
    else $error("X/Z on data_out for known data_in");

  // Functional coverage: ranges
  cover property (@(data_in) (!$isunknown(data_in)) && (data_in inside {[0:4]})   && (data_out==2'b00));
  cover property (@(data_in) (!$isunknown(data_in)) && (data_in inside {[5:8]})   && (data_out==2'b01));
  cover property (@(data_in) (!$isunknown(data_in)) && (data_in inside {[9:12]})  && (data_out==2'b10));
  cover property (@(data_in) (!$isunknown(data_in)) && (data_in inside {[13:15]}) && (data_out==2'b11));

  // Boundary coverage
  cover property (@(data_in) (data_in==4)  && (data_out==2'b00));
  cover property (@(data_in) (data_in==5)  && (data_out==2'b01));
  cover property (@(data_in) (data_in==8)  && (data_out==2'b01));
  cover property (@(data_in) (data_in==9)  && (data_out==2'b10));
  cover property (@(data_in) (data_in==12) && (data_out==2'b10));
  cover property (@(data_in) (data_in==13) && (data_out==2'b11));

endmodule

bind data_converter data_converter_sva u_data_converter_sva (.data_in(data_in), .data_out(data_out));