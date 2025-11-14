// SVA for cf_mul: functional equivalence, latency, X-checks, and targeted coverage.
// Bind this file to cf_mul or include inside the module under `ifdef SVA.

`ifndef CF_MUL_SVA
`define CF_MUL_SVA

module cf_mul_sva #(parameter DELAY_DATA_WIDTH=16)
(
  input logic               clk,
  input logic [16:0]        data_a,
  input logic [7:0]         data_b,
  input logic [24:0]        data_p,
  input logic [DELAY_DATA_WIDTH-1:0] ddata_in,
  input logic [DELAY_DATA_WIDTH-1:0] ddata_out
);

  // Warm-up: validate assertions only after 3 clocks (pipeline depth)
  logic [2:0] init_sr;
  always_ff @(posedge clk) init_sr <= {init_sr[1:0], 1'b1};
  wire valid3 = init_sr[2];

  // Reference model (matches RTL’s Booth-like partial-product construction)
  function automatic signed [23:0] sext17_to24(input logic [16:0] v);
    return {{7{v[16]}}, v};
  endfunction

  function automatic signed [23:0] booth24(input logic [15:0] a16, input logic [7:0] b8);
    logic [16:0] one_p_17 = {1'b0, a16};
    logic [16:0] one_n_17 = ~one_p_17 + 17'd1;
    signed [23:0] one_p = sext17_to24(one_p_17);
    signed [23:0] one_n = sext17_to24(one_n_17);
    signed [23:0] two_p = one_p <<< 1;
    signed [23:0] two_n = one_n <<< 1;
    signed [23:0] acc    = '0;

    unique case (b8[1:0])
      2'b11: acc += one_n;
      2'b10: acc += two_n;
      2'b01: acc += one_p;
      default: ;
    endcase

    unique case (b8[3:1])
      3'b011: acc += (two_p <<< 2);
      3'b100: acc += (two_n <<< 2);
      3'b001, 3'b010: acc += (one_p <<< 2);
      3'b101, 3'b110: acc += (one_n <<< 2);
      default: ;
    endcase

    unique case (b8[5:3])
      3'b011: acc += (two_p <<< 4);
      3'b100: acc += (two_n <<< 4);
      3'b001, 3'b010: acc += (one_p <<< 4);
      3'b101, 3'b110: acc += (one_n <<< 4);
      default: ;
    endcase

    unique case (b8[7:5])
      3'b011: acc += (two_p <<< 6);
      3'b100: acc += (two_n <<< 6);
      3'b001, 3'b010: acc += (one_p <<< 6);
      3'b101, 3'b110: acc += (one_n <<< 6);
      default: ;
    endcase

    if (b8[7]) acc += (one_p <<< 8);
    return acc;
  endfunction

  // Golden functional and latency check (3-cycle pipeline)
  property p_func_latency;
    @(posedge clk) valid3 |->
      ( data_p[24]          == $past(data_a[16], 3) ) &&
      ( data_p[23:0]        == booth24($past(data_a[15:0], 3), $past(data_b, 3)) ) &&
      ( ddata_out           == $past(ddata_in, 3) );
  endproperty
  assert property (p_func_latency);

  // No-X checks (inputs each cycle; outputs after pipeline warm-up)
  assert property (@(posedge clk) !$isunknown({data_a, data_b, ddata_in}));
  assert property (@(posedge clk) valid3 |-> !$isunknown({data_p, ddata_out}));

  // Targeted coverage: exercise all recode patterns across the windows and MSB add
  // 2-bit window patterns
  cover property (@(posedge clk) data_b[1:0] == 2'b01);
  cover property (@(posedge clk) data_b[1:0] == 2'b10);
  cover property (@(posedge clk) data_b[1:0] == 2'b11);

  // 3-bit window patterns (hit in any of the three overlapping windows)
  cover property (@(posedge clk) ((data_b[3:1]==3'b001)||(data_b[5:3]==3'b001)||(data_b[7:5]==3'b001)));
  cover property (@(posedge clk) ((data_b[3:1]==3'b010)||(data_b[5:3]==3'b010)||(data_b[7:5]==3'b010)));
  cover property (@(posedge clk) ((data_b[3:1]==3'b011)||(data_b[5:3]==3'b011)||(data_b[7:5]==3'b011)));
  cover property (@(posedge clk) ((data_b[3:1]==3'b100)||(data_b[5:3]==3'b100)||(data_b[7:5]==3'b100)));
  cover property (@(posedge clk) ((data_b[3:1]==3'b101)||(data_b[5:3]==3'b101)||(data_b[7:5]==3'b101)));
  cover property (@(posedge clk) ((data_b[3:1]==3'b110)||(data_b[5:3]==3'b110)||(data_b[7:5]==3'b110)));

  // MSB add term used
  cover property (@(posedge clk) data_b[7]);

  // Extremes and sign coverage
  cover property (@(posedge clk) data_a[16]);        // negative sign seen at output after 3 cycles
  cover property (@(posedge clk) !data_a[16]);       // positive sign seen
  cover property (@(posedge clk) data_a[15:0]==16'h0000);
  cover property (@(posedge clk) data_a[15:0]==16'hFFFF);
  cover property (@(posedge clk) data_b==8'h00);
  cover property (@(posedge clk) data_b==8'hFF);

endmodule

// Bind into DUT
bind cf_mul cf_mul_sva #(.DELAY_DATA_WIDTH(DELAY_DATA_WIDTH)) cf_mul_sva_i (.*);

`endif