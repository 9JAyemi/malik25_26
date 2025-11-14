// SVA/coverage for fifo_counter (bindable, clockless-comb friendly)
module fifo_counter_sva(
  input  logic        empty,
  input  logic        ge2_free,
  input  logic        ge3_free,
  input  logic [1:0]  input_tm_cnt,
  input  logic [4:0]  fifo_cnt_inc
);

  // Combinational checker and procedural coverage
  always @* begin
    // Known-when-inputs-known
    if (!$isunknown({empty,ge2_free,ge3_free,input_tm_cnt}))
      assert (!$isunknown(fifo_cnt_inc)) else $error("fifo_cnt_inc X/Z with known inputs");

    // Golden mapping (priority + value)
    automatic logic [4:0] exp;
    exp = 'x;
    if (empty)                                exp = {3'b000,input_tm_cnt};
    else if (ge3_free && (input_tm_cnt==2'd3)) exp = 5'd2;
    else if (ge2_free && (input_tm_cnt>=2))    exp = 5'd1;
    else if (input_tm_cnt>=1)                  exp = 5'd0;
    else                                       exp = 5'd31;

    assert (fifo_cnt_inc === exp)
      else $error("fifo_cnt_inc mismatch: exp=%0d got=%0d", exp, fifo_cnt_inc);

    // Sanity/range and explicit priority points
    if (empty) begin
      assert (fifo_cnt_inc[4:2]==3'b000 && fifo_cnt_inc[1:0]==input_tm_cnt)
        else $error("empty mapping wrong");
    end else begin
      assert (fifo_cnt_inc inside {5'd0,5'd1,5'd2,5'd31})
        else $error("illegal value when !empty");
      if (ge3_free && (input_tm_cnt==2'd3))
        assert (fifo_cnt_inc==5'd2) else $error("ge3_free case wrong");
      if (!(ge3_free && (input_tm_cnt==2'd3)) && ge2_free && (input_tm_cnt>=2))
        assert (fifo_cnt_inc==5'd1) else $error("ge2_free case wrong");
      if (!(ge3_free && (input_tm_cnt==2'd3)) && !(ge2_free && (input_tm_cnt>=2)) && (input_tm_cnt>=1))
        assert (fifo_cnt_inc==5'd0) else $error(">=1 fallback wrong");
      if (input_tm_cnt==2'd0)
        assert (fifo_cnt_inc==5'd31) else $error("else case wrong");
    end

    // Functional coverage (procedural, clockless)
    cover (empty && input_tm_cnt==2'd0 && fifo_cnt_inc==5'd0);
    cover (empty && input_tm_cnt==2'd1 && fifo_cnt_inc==5'd1);
    cover (empty && input_tm_cnt==2'd2 && fifo_cnt_inc==5'd2);
    cover (empty && input_tm_cnt==2'd3 && fifo_cnt_inc==5'd3);

    cover (!empty && ge3_free && input_tm_cnt==2'd3 && fifo_cnt_inc==5'd2);
    cover (!empty && ge2_free && (input_tm_cnt>=2) && !(ge3_free && input_tm_cnt==2'd3) && fifo_cnt_inc==5'd1);
    cover (!empty && (input_tm_cnt>=1) && !(ge3_free && input_tm_cnt==2'd3) && !(ge2_free && (input_tm_cnt>=2)) && fifo_cnt_inc==5'd0);
    cover (!empty && (input_tm_cnt==2'd0) && fifo_cnt_inc==5'd31);

    // Priority win when both frees high on 3
    cover (!empty && ge3_free && ge2_free && input_tm_cnt==2'd3 && fifo_cnt_inc==5'd2);
  end

endmodule

bind fifo_counter fifo_counter_sva sva(
  .empty(empty),
  .ge2_free(ge2_free),
  .ge3_free(ge3_free),
  .input_tm_cnt(input_tm_cnt),
  .fifo_cnt_inc(fifo_cnt_inc)
);