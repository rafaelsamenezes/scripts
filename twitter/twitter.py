from searchtweets import load_credentials, gen_rule_payload, ResultStream

# 1. Run this first: pip3 install --user searchtweets
# 2. Change these variables
QUERY = "@V2019N (#COVID19 OR patients OR pandemic OR hospitalization OR virus OR corona OR (tested positive) OR infected OR vaccine)"
RESULTS_PER_CALL = 10 # Be careful with the limits!
MAX_RESULTS = 10 # Be careful with the limits!
FROM_DATE = "2020-01-01"
TO_DATE = "2020-03-31"
OUTPUT = 'tweetsData.txt'

# 3. Run the script and use excel to import as a tabulation file

## IGNORE THIS

premium_search_args = load_credentials("credentials.yml",
                                       yaml_key="search_tweets_api",
                                       env_overwrite=False)


rule = gen_rule_payload(QUERY, results_per_call=RESULTS_PER_CALL, from_date=FROM_DATE, to_date=TO_DATE)
rs = ResultStream(rule_payload=rule,
                  max_results=MAX_RESULTS,
                  **premium_search_args)


with open(OUTPUT, 'a', encoding='utf-8') as f:
    line = "criado_em\ttweet\tusuario\tidioma\n"
    f.write(line)
    for tweet in rs.stream():
        created_at = tweet["created_at"]
        text = tweet["text"].replace('\n', ' ').replace('\r', '').replace('\t', '')
        user = tweet["user"]["name"]
        lang = tweet["lang"]
        line = f"{created_at}\t{text}\t{user}\t{lang}\n"
        if line != "\n":
            f.write(line)

print('done')