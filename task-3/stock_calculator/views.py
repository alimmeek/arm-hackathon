from django.shortcuts import render
import requests
from datetime import datetime
import matplotlib.pyplot as plt
import seaborn

# Create your views here.
def dashboard(request):
    if request.method == 'POST':
        amount = request.POST.get('amount')
        date = request.POST.get('date')
        symbol = request.POST.get('name')

        api_key = '6BRPDCS4W0TGFI6S'

        if not amount or not date:
            error_message = "Both amount and date fields are required."
            return render(request, 'dashboard.html', {'error_message': error_message})        

        # Get all data for the month. (It doesn't let us get the data for a specific day.)
        r = requests.get(f"https://www.alphavantage.co/query?function=TIME_SERIES_INTRADAY&symbol={symbol}&interval=5min&month={date[0:-3]}&outputsize=full&apikey={api_key}")
        data = r.json()

        # Extract the time series
        time_series = data["Time Series (5min)"]

        # The date will have multiple keys (2009-01-01 08:00, 2009-01-01 08:05, etc.).
        all_keys_for_date = [key for key in time_series.keys() if key.startswith(date)]

        # If data for the date doesn't exist, then return an error.
        if len(all_keys_for_date) == 0:
            return render(request, 'dashboard.html', {'error_message': "There is no data for that date."}) 

        # Get the earliest key for the date (as there are multiple, e.g., 2009-01-01 08:00, 2009-01-01 08:05).
        earliest_key_for_date = all_keys_for_date[-1]
        open_stock_value = time_series[earliest_key_for_date]['1. open']

        fraction_of_stock = float(amount) / float(open_stock_value)

        # Get today's stock value, multiply it by fraction_of_stock, and get result - converted_amount
        r = requests.get(f"https://www.alphavantage.co/query?function=TIME_SERIES_INTRADAY&symbol={symbol}&interval=5min&outputsize=full&apikey={api_key}")
        data = r.json()

        # Extract the time series
        latest_time_series = data["Time Series (5min)"]
        latest_date = next(iter(latest_time_series))
        latest_open_stock_value = latest_time_series[latest_date]['1. open']

        difference = (float(latest_open_stock_value) * fraction_of_stock) - float(amount)
        if difference >= 0:
            output_data = f"You gained £{abs(difference)}."
        else:
            output_data = f"You lost £{abs(difference)}."

        return render(request, 'dashboard.html', {'output_data': output_data, 'date': date, 
                                                  'open': open_stock_value, 'latest_open': latest_open_stock_value, 
                                                  'amount': amount, 'symbol': symbol})

    return render(request, 'dashboard.html')


def graph(request):
    api_key = '6BRPDCS4W0TGFI6S'

    symbol = request.GET.get('symbol') or 'IBM'
    
    url = f'https://www.alphavantage.co/query?function=TIME_SERIES_DAILY_ADJUSTED&symbol={symbol}&apikey={api_key}'
    r = requests.get(url)

    dis_data = r.json()


    dis_dicts = dis_data['Time Series (Daily)']
    dis_dates, highs, lows = [], [], []

    for date in dis_dicts:
        dis_dates.append(datetime.strptime(date, '%Y-%m-%d'))
        highs.append(float(dis_dicts[date]['2. high']))
        lows.append(float(dis_dicts[date]['3. low']))
   
   
    plt.figure(figsize=(10, 6))
    plt.plot(dis_dates, highs, color='red', alpha=0.6, label='Highs')
    plt.plot(dis_dates, lows, color='blue', alpha=0.6, label='Lows')
    plt.fill_between(dis_dates, highs, lows, color='blue', alpha=0.15)

    # Set plot title and labels
    plt.title("Daily high and low stock prices for the last 100 days")
    plt.xlabel('Date')
    plt.ylabel('Price (USD)')
    plt.legend()

    # Save the plot as an image
    plt.savefig('static/plot.png')
    # plt.show()

    # fig, ax = plt.subplots()
    # ax.plot(dis_dates, highs, c='red', alpha=0.6)
    # ax.plot(dis_data, lows, c='blue', alpha=0.6)
    # ax.fill_between(dis_dates, highs, lows, facecolor='blue', alpha=0.15)

    # ax.set_title(f"Daily high and low stock prices, for last 100 days")
    # ax.set_xlabel('',fontsize=16)


    # plt.savefig('plot.png')
    # plt.show()

    return render(request, 'dashboard_2.html')