module arbiter (
    input  logic clk,
    input  logic resetn,

    input  logic [2:0] r,
    
    output logic [2:0] g
);

parameter A = 2'b00, B = 2'b01, C = 2'b10, D = 2'b11;

logic [1:0] next_state;
logic [1:0] curr_state;

logic [2:0] g_next;
logic [2:0] g_q;

always_comb begin
    next_state = curr_state;
    case (curr_state)
        A : begin
            if (r[0]) begin
                next_state = B;
            end else if (r[1]) begin
                next_state = C;
            end else if (r[2]) begin
                next_state = D;
            end
        end

        B : begin
            if (~r[0]) begin
                next_state = A;
            end
        end

        C : begin
            if (~r[1]) begin
                next_state = A;
            end
        end

        D : begin
            if (~r[2]) begin
                next_state = A;
            end
        end
    endcase
end

always_comb begin
    g_next = g_q;
    case (curr_state)
        A : g_next = 3'b000;

        B : g_next = 3'b001;

        C : g_next = 3'b010;

        D : g_next = 3'b100;
    endcase
end

always_ff @(posedge clk or negedge resetn) begin
    if (~resetn) begin
        curr_state <= A;
        g_q <= 3'b000;
    end else begin
        curr_state <= next_state;
        g_q <= g_next;
    end
end

assign g = g_q;

endmodule